import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Properties.Common

namespace Properties.IdealSoundness

open PlutusCore.UPLC.Term (Program)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Address Datum Redeemer ScriptContext StakingCredential
                          TxInfo TxInInfo TxOut TxOutRef Value OutputDatum PubKeyHash findOwnInput validScriptContext valueOf txSignedBy)

set_option warn.sorry false

def spendsInput (ctx : ScriptContext) (input : TxInInfo) : Prop :=
  findOwnInput ctx = some input

def hasOutput (ctx : ScriptContext) (out : TxOut) : Prop :=
  out ∈ ctx.scriptContextTxInfo.txInfoOutputs

structure IdealOrderDatum where
  owner : ByteString
  amount : Int
  policyId : ByteString
  assetName : ByteString

/--
  Parse given Plutus data and return order information.
  The first four fields are read.
  More fields can be present as they are ignored.
  Returns none if the data is not as expected.
--/
def orderDatum (orderData : Data) : Option IdealOrderDatum :=
  match orderData with
  | Data.Constr 0
      ( Data.B owner ::
        Data.I amount ::
        Data.B policyId ::
        Data.B assetName ::
        _
      ) => some
      { owner := owner
        amount := amount
        policyId := policyId
        assetName := assetName
      }
  | _ => none

/--
  Checks that `utxo` is a well-formed order UTxO.
--/
def validOrder (utxo : TxOut) : Prop :=
  utxo.txOutAddress.addressCredential = .ScriptCredential "fake_script_hash_28bytes!!!!" ∧
  (if let .OutputDatum datum := utxo.txOutDatum then
    if let some oDatum := orderDatum datum then
      -- TODO: check correct lengths for bytestrings oDatum.owner and oDatum.policyID
      oDatum.amount >= 0
    else
      -- datum is not well-formed
      false
  else
    -- datum is not inline
    false) ∧
  utxo.txOutReferenceScript = none

/--
  Checks that `contUtxo` is a correct output for resolving `utxo` order.
  In particular, it is ensured `validOrder contUtxo` (it is a valid order).

  Preconditions:
  - `validOrder utxo`
--/
def validResolve (utxo contUtxo : TxOut) : Prop :=
  -- parse input datum
  if let .OutputDatum inDatum := utxo.txOutDatum then
    if let some inDatum := orderDatum inDatum then
      if let .OutputDatum outDatum := contUtxo.txOutDatum then
        if let some outDatum := orderDatum outDatum then

          -- check address
          contUtxo.txOutAddress = utxo.txOutAddress

          -- check datum (only relevant fields)
          ∧ outDatum = inDatum

          -- check value
          ∧ let askedPolicy := inDatum.policyId
            let askedAssetName := inDatum.assetName
            valueOf askedPolicy askedAssetName contUtxo.txOutValue ≥
            valueOf askedPolicy askedAssetName utxo.txOutValue + inDatum.amount

          -- check ref script
          ∧ contUtxo.txOutReferenceScript = none
        else
          false
      else
        false
    else
      -- false precondition: input datum is not well-formed
      false
  else
    -- false precondition: input datum is not inline
    false

def orderOwner (utxo : TxOut) : Option ByteString :=
  if let .OutputDatum datum := utxo.txOutDatum then
    if let some oDatum := orderDatum datum then
      oDatum.owner
    else
      -- datum is not well-formed
      none
  else
    -- datum is not inline
    none

def ideal_spend_soundness_theorem
  (orderValidator : ScriptContext → Prop)
  : Prop :=
  ∀
    (ctx : ScriptContext)
    (utxo : TxOut)
    (utxoRef : TxOutRef),
    validScriptContext ctx
    ∧ spendsInput ctx ⟨utxoRef, utxo⟩
    ∧ validOrder utxo
    ∧ orderValidator ctx
    →
      -- close operation
      (∃ (owner : ByteString),
        some owner = orderOwner utxo
        ∧ txSignedBy owner (ctx.scriptContextTxInfo))
      ∨
      -- resolve operation
      (∃ (contUtxo : TxOut),
        hasOutput ctx contUtxo
        ∧ validResolve utxo contUtxo)

end Properties.IdealSoundness
