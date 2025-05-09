import {
  fromText,
  Addresses,
  Crypto,
  Data,
  Emulator,
  Lucid
} from "https://deno.land/x/lucid@0.20.5/mod.ts";
import {
  OrderOrderSpend,
  OrderOrderDatum,
} from "../plutus.ts";

const tokenAPolicy = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const tokenAAsset = fromText("A");
const tokenA = tokenAPolicy + tokenAAsset;

const tokenBPolicy = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const tokenBAsset = fromText("B");
const tokenB = tokenBPolicy + tokenBAsset;

// https://github.com/spacebudz/lucid/blob/main/examples/emulate_something.ts
// seller 1
const privateKey1 = Crypto.generatePrivateKey();
const address1 = Addresses.credentialToAddress(
  { Emulator: 0 },
  Crypto.privateKeyToDetails(privateKey1).credential,
);

// seller 2
const privateKey2 = Crypto.generatePrivateKey();
const address2 = Addresses.credentialToAddress(
  { Emulator: 0 },
  Crypto.privateKeyToDetails(privateKey2).credential,
);

const emulator = new Emulator([
  { // seller 1
    address: address1,
    assets: {
      lovelace: 3000000000n,
      [tokenA]: 10000n,
    }
  },
  { // seller 2
    address: address2,
    assets: {
      lovelace: 3000000000n,
      [tokenB]: 10000n,
    }
  },
]);

const lucid1 = new Lucid({
  provider: emulator,
  wallet: { PrivateKey: privateKey1 },
});

const lucid2 = new Lucid({
  provider: emulator,
  wallet: { PrivateKey: privateKey2 },
});

//
// CREATE ORDER 1: OFFER 1234 A FOR 4242 B
//
const orderValidator = new OrderOrderSpend();
const orderAddress = lucid1.newScript(orderValidator).toAddress();
const orderHash = lucid1.newScript(orderValidator).toHash();
const validityToken = orderHash + fromText("val");

const { payment } = Addresses.inspect(address1);
const orderDatum: OrderOrderDatum = {
  owner: payment.hash,
  amount: 4242n,
  policyId: tokenBPolicy,
  assetName: tokenBAsset,
  tag: {
    transactionId: '0000000000000000000000000000000000000000000000000000000000000000',
    outputIndex: 0n,
  },
}

const createTx = await lucid1
  .newTx()
  .attachScript(orderValidator)
  .mint(
    {
      [validityToken]: 1n,
    },
    Data.void()
  )
  .payToContract(
    orderAddress,
    { Inline: Data.to(orderDatum, OrderOrderSpend.datum) },
    {
      [validityToken]: 1n,
      [tokenA]: 1234n,
    }
  )
  .commit();

const signedCreateTx = await createTx.sign().commit();
const createTxHash = await signedCreateTx.submit();

// console.log("CREATE TX:", signedCreateTx.toString());

emulator.awaitTx(createTxHash);

//
// CREATE ORDER 2: OFFER 4242 B FOR 1234 A
//
const { payment: payment2 } = Addresses.inspect(address2);
const orderDatum2: OrderOrderDatum = {
  owner: payment2.hash,
  amount: 1234n,
  policyId: tokenAPolicy,
  assetName: tokenAAsset,
  tag: {
    transactionId: '0000000000000000000000000000000000000000000000000000000000000000',
    outputIndex: 1n,
  },
}

const createTx2 = await lucid2
  .newTx()
  .attachScript(orderValidator)
  .mint(
    {
      [validityToken]: 1n,
    },
    Data.void()
  )
  .payToContract(
    orderAddress,
    { Inline: Data.to(orderDatum2, OrderOrderSpend.datum) },
    {
      [validityToken]: 1n,
      [tokenB]: 4242n,
    }
  )
  .commit();

const signedCreateTx2 = await createTx2.sign().commit();
const createTxHash2 = await signedCreateTx2.submit();

// console.log("CREATE TX:", signedCreateTx2.toString());

emulator.awaitTx(createTxHash2);



//
// RESOLVE BOTH ORDERS (DONE BY SELLER 2)
//
const [order] = await lucid2.utxosByOutRef([{
  txHash: createTxHash,
  outputIndex: 0,
}]);
const [order2] = await lucid2.utxosByOutRef([{
  txHash: createTxHash2,
  outputIndex: 0,
}]);

const resolveOrderDatum: OrderOrderDatum = {
  owner: payment.hash,
  amount: 4242n,
  policyId: tokenBPolicy,
  assetName: tokenBAsset,
  tag: {
    transactionId: createTxHash,
    outputIndex: 0n,
  },
}
const resolveOrderDatum2: OrderOrderDatum = {
  owner: payment2.hash,
  amount: 1234n,
  policyId: tokenAPolicy,
  assetName: tokenAAsset,
  tag: {
    transactionId: createTxHash2,
    outputIndex: 0n,
  },
}

const resolveTx = await lucid2
  .newTx()
  .attachScript(orderValidator)
  .collectFrom(
    [order],
    Data.to({Resolve: [0n]}, OrderOrderSpend.redeemer)
  )
  .collectFrom(
    [order2],
    Data.to({Resolve: [1n]}, OrderOrderSpend.redeemer)
  )
  .payToContract(
    orderAddress,
    { Inline: Data.to(resolveOrderDatum, OrderOrderSpend.datum) },
    {
      [validityToken]: 1n,
      [tokenB]: 4242n,
    }
  )
  .payToContract(
    orderAddress,
    { Inline: Data.to(resolveOrderDatum2, OrderOrderSpend.datum) },
    {
      [validityToken]: 1n,
      [tokenA]: 1234n,
    }
  )
  .commit();

const signedResolveTx = await resolveTx.sign().commit();
const resolveTxHash = await signedResolveTx.submit();

// console.log("RESOLVE TX:", signedResolveTx.toString());
console.log("RESOLVE TX HASH:", resolveTxHash);

emulator.awaitTx(resolveTxHash);


//
// CLOSE ORDER 1 (DONE BY SELLER 1)
//
const [resolvedOrder1] = await lucid1.utxosByOutRef([{
  txHash: resolveTxHash,
  outputIndex: 0,
}]);

const closeTx1 = await lucid1
  .newTx()
  .attachScript(orderValidator)
  .collectFrom(
    [resolvedOrder1],
    Data.to("Close", OrderOrderSpend.redeemer)
  )
  .mint(
    {
      [validityToken]: -1n,
    },
    Data.void()
  )
  // following: https://github.com/spacebudz/lucid/blob/cb3435ba65e0131b464769851f1e1c024564d155/src/lucid/tx.ts#L229
  .addSigner("{{own.payment}}")
  .commit();

const signedCloseTx1 = await closeTx1.sign().commit();
const signedCloseHash1 = await signedCloseTx1.submit();

// console.log("CLOSE TX:", signedCloseTx1.toString());

emulator.awaitTx(signedCloseHash1);


//
// CLOSE ORDER 2 (DONE BY SELLER 2)
//
const [resolvedOrder2] = await lucid2.utxosByOutRef([{
  txHash: resolveTxHash,
  outputIndex: 1,  // THIS IS 1
}]);

const closeTx2 = await lucid2
  .newTx()
  .attachScript(orderValidator)
  .collectFrom(
    [resolvedOrder2],
    Data.to("Close", OrderOrderSpend.redeemer)
  )
  .mint(
    {
      [validityToken]: -1n,
    },
    Data.void()
  )
  // following: https://github.com/spacebudz/lucid/blob/cb3435ba65e0131b464769851f1e1c024564d155/src/lucid/tx.ts#L229
  .addSigner("{{own.payment}}")
  .commit();

const signedCloseTx2 = await closeTx2.sign().commit();
const signedCloseHash2 = await signedCloseTx2.submit();

emulator.awaitTx(signedCloseHash2);
