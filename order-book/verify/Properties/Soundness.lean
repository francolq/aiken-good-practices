import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Properties.Common

namespace Properties.Soundness

open PlutusCore.UPLC.Term (Program)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open Properties.Common (validatorAccepts)
open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Address Datum Redeemer ScriptContext TxInfo TxInInfo
                          TxOut Value OutputDatum PubKeyHash validScriptContext
                          lovelaceValue valueOf singleton add)

set_option warn.sorry false

structure OrderDatum where
  owner : ByteString
  amount : Int
  policyId : ByteString
  assetName : ByteString

def baseTxInfo: TxInfo :=
  { txInfoInputs := []
    txInfoReferenceInputs := []
    txInfoOutputs := []
    txInfoFee := 0
    txInfoMint := []
    txInfoTxCerts := []
    txInfoWdrl := []
    txInfoValidRange := IsData.toData (none : Option Int)
    txInfoSignatories := []
    txInfoRedeemers := []
    txInfoData := []
    txInfoId := "txid_placeholder_32bytes!!!!!!!!"
    txInfoVotes := []
    txInfoProposalProcedures := []
    txInfoCurrentTreasuryAmount := IsData.toData (none : Option Int)
    txInfoTreasuryDonation := IsData.toData (none : Option Int)
  }

def validOrder (utxo : TxOut) (datum : OrderDatum) : Prop :=
  utxo.txOutAddress = ⟨.ScriptCredential "fake_script_hash_28bytes!!!!", none⟩
  --  ∧
  -- utxo.txOutDatum = .OutputDatum (orderData datum)

def validResolve (utxo contUtxo : TxOut) (datum : OrderDatum) : Prop :=
  contUtxo.txOutAddress = utxo.txOutAddress ∧
  contUtxo.txOutDatum = utxo.txOutDatum ∧
  let askedPolicy := datum.policyId
  let askedAssetName := datum.assetName
  valueOf askedPolicy askedAssetName contUtxo.txOutValue ≥
  valueOf askedPolicy askedAssetName utxo.txOutValue + datum.amount

def hasOutputs (ctx : ScriptContext) (outs : List TxOut) : Prop :=
  ctx.scriptContextTxInfo.txInfoOutputs = outs

def hasInputs (ctx : ScriptContext) (ins : List TxInInfo) : Prop :=
  ctx.scriptContextTxInfo.txInfoInputs = ins

def orderValue (lovelace a : Int) : Value :=
    if a = 0 then
      [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)])]
    else
      [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)]),
        (Data.B "fake_policyA_hash_28bytes!!!",
        Data.Map [(Data.B "fake_asset_nameA", Data.I a)])]

def orderValue2 (lovelace a b : Int) : Value :=
    if a = 0 ∧ b = 0 then
      [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)])]
    else if a = 0 then
      [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)]),
        (Data.B "fake_policyB_hash_28bytes!!!",
        Data.Map [(Data.B "fake_asset_nameB", Data.I b)])]
    else if b = 0 then
      [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)]),
        (Data.B "fake_policyA_hash_28bytes!!!",
        Data.Map [(Data.B "fake_asset_nameA", Data.I a)])]
    else
      [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)]),
        (Data.B "fake_policyA_hash_28bytes!!!",
        Data.Map [(Data.B "fake_asset_nameA", Data.I a)]),
        (Data.B "fake_policyB_hash_28bytes!!!",
        Data.Map [(Data.B "fake_asset_nameB", Data.I b)])]

def spend_sound_theorem
  (validator : Program)
  (redeemer : Redeemer)
  (orderData : OrderDatum -> Data) : Prop :=
    ∀ (outAddr : Address)
      (inLovelace inA : Int)         -- input value
      (outLovelace outA outB : Int)  -- output value
      (someSignatory : PubKeyHash)
      (outDatum : OrderDatum)
      ,
    let inDatum : OrderDatum := {
      owner := "fake_owner_pkh"
      amount := 10  -- TODO: generalize!!
      policyId := "fake_policyB_hash_28bytes!!!"
      assetName := "fake_asset_nameB"
    }
    let inDatumData := orderData inDatum
    let outDatumData := orderData outDatum
    let utxoRef := ⟨"txid_placeholder_32bytes!!!!!!!!", 0⟩
    let utxo : TxOut :=
      ⟨ ⟨.ScriptCredential "fake_script_hash_28bytes!!!!", none⟩,
        orderValue inLovelace inA,  -- TODO: can I make this more general?
        .OutputDatum inDatumData,
        none
      ⟩
    let someOutput : TxOut :=
      ⟨ outAddr,
        orderValue2 outLovelace outA outB,  -- TODO: can I make this more general?
        .OutputDatum outDatumData,
        none
      ⟩
    let txInfo :=
      { baseTxInfo with
        txInfoInputs := [⟨utxoRef, utxo⟩]
        txInfoOutputs := [someOutput]
        txInfoRedeemers := [(.Spending utxoRef, redeemer)]
        txInfoSignatories := [someSignatory]
      }
    let ctx : ScriptContext :=
      { scriptContextTxInfo := txInfo
        scriptContextRedeemer := redeemer
        scriptContextScriptInfo := .SpendingScript utxoRef inDatumData
      }
    -- XXX: this is returning false (but is not needed):
    -- validScriptContext ctx ∧
    -- hasInputs ctx [⟨utxoRef, utxo⟩] ∧  -- already covered
    -- constrainedUtxo utxo inValue inDatumData ∧
    inLovelace > 0 ∧
    outLovelace > 0 ∧
    validOrder utxo inDatum ∧
    validatorAccepts ctx validator →
        -- close operation
        someSignatory = inDatum.owner
      ∨
        -- resolve operation
        -- ∃ (contUtxo : TxOut),  contUtxo = someOutput
        (let contUtxo := someOutput
        hasOutputs ctx [contUtxo]
        ∧ validOrder contUtxo inDatum
        ∧ validResolve utxo contUtxo inDatum)

end Properties.Soundness
