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
                          TxOut Value OutputDatum validScriptContext
                          lovelaceValue valueOf singleton add)

set_option warn.sorry false

structure OrderDatum where
  owner : ByteString
  amount : Int
  policyId : ByteString
  assetName : ByteString

-- FIXME: won't work with OrderV2 because of the tag
def orderData (d : OrderDatum) : Data :=
  Data.Constr 0
  [ Data.B d.owner,
    Data.I d.amount,
    Data.B d.policyId,
    Data.B d.assetName ]

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
  utxo.txOutAddress = ⟨.ScriptCredential "fake_script_hash_28bytes!!!!", none⟩ ∧
  utxo.txOutDatum = .OutputDatum (orderData datum)

def validTransition (utxo contUtxo : TxOut) (datum : OrderDatum) : Prop :=
  contUtxo.txOutAddress = utxo.txOutAddress ∧
  contUtxo.txOutDatum = utxo.txOutDatum ∧
  valueOf datum.policyId datum.assetName contUtxo.txOutValue ≥ 0

def hasOutputs (ctx : ScriptContext) (outs : List TxOut) : Prop :=
  ctx.scriptContextTxInfo.txInfoOutputs = outs

def hasInputs (ctx : ScriptContext) (ins : List TxInInfo) : Prop :=
  ctx.scriptContextTxInfo.txInfoInputs = ins

def spend_sound_theorem (validator : Program) (redeemer : Redeemer) : Prop :=
    ∀ (outAddr : Address)
      (inLovelace : Int)
      (aAmount : Int)
      ,
    aAmount = 10 ∧
    -- let aAmount := 10
    let inDatum : OrderDatum := {
      owner := "fake_owner_pkh"
      amount := 10  -- TODO: generalize!!
      policyId := "fake_policyB_hash_28bytes!!!"
      assetName := "fake_asset_nameB"
    }
    let inDatumData := orderData inDatum
    let utxoRef := ⟨"txid_placeholder_32bytes!!!!!!!!", 0⟩
    let inValue := lovelaceValue inLovelace |>
                   add "fake_policyA_hash_28bytes!!!" "fake_asset_nameA" aAmount
    let utxo : TxOut :=
      ⟨ ⟨.ScriptCredential "fake_script_hash_28bytes!!!!", none⟩,
        inValue,  -- TODO: fix this
        .OutputDatum inDatumData,
        none
      ⟩
    let someOutput : TxOut :=
      ⟨ outAddr,
        lovelaceValue 0 |>
        add inDatum.policyId inDatum.assetName inDatum.amount, -- TODO: THIS IS CHEATING
        .OutputDatum inDatumData,                              -- TODO: THIS IS CHEATING
        none
      ⟩
    let txInfo :=
      { baseTxInfo with
        txInfoInputs := [⟨utxoRef, utxo⟩]
        txInfoOutputs := [someOutput]
        txInfoRedeemers := [(.Spending utxoRef, redeemer)]
        -- txInfoSignatories := [someSignatory]  -- TODO
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
    validOrder utxo inDatum ∧
    validatorAccepts ctx validator →
    -- ∃ (contUtxo : TxOut),  contUtxo = someOutput
      let contUtxo := someOutput
      hasOutputs ctx [contUtxo]
      ∧ validOrder contUtxo inDatum
      ∧ validTransition utxo contUtxo inDatum

end Properties.Soundness
