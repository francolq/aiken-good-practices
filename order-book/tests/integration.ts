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
// seller
const privateKey1 = Crypto.generatePrivateKey();
const address1 = Addresses.credentialToAddress(
  { Emulator: 0 },
  Crypto.privateKeyToDetails(privateKey1).credential,
);

// buyer
const privateKey2 = Crypto.generatePrivateKey();
const address2 = Addresses.credentialToAddress(
  { Emulator: 0 },
  Crypto.privateKeyToDetails(privateKey2).credential,
);

const emulator = new Emulator([
  { // seller
    address: address1,
    assets: {
      lovelace: 3000000000n,
      [tokenA]: 10000n,
    }
  },
  { // buyer
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
// CREATE ORDER: OFFER 1234 A FOR 4242 B
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
  assetName:tokenBAsset,
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
console.log("CREATE ORDER TX HASH:", createTxHash);

emulator.awaitTx(createTxHash);

//
// RESOLVE ORDER
//
const [order] = await lucid2.utxosByOutRef([{
  txHash: createTxHash,
  outputIndex: 0,
}]);

const orderDatum2: OrderOrderDatum = {
  owner: payment.hash,
  amount: 4242n,
  policyId: tokenBPolicy,
  assetName:tokenBAsset,
  tag: {
    transactionId: createTxHash,
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
  .payToContract(
    orderAddress,
    { Inline: Data.to(orderDatum2, OrderOrderSpend.datum) },
    {
      [validityToken]: 1n,
      [tokenB]: 4300n,
    }
  )
  .commit();

const signedResolveTx = await resolveTx.sign().commit();
const resolveTxHash = await signedResolveTx.submit();

// console.log("RESOLVE TX:", signedResolveTx.toString());
console.log("RESOLVE TX HASH:", resolveTxHash);
