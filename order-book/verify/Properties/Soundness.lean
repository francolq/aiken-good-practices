import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Properties.Common

namespace Properties.Soundness

open PlutusCore.UPLC.Term (Program)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open Properties.Common (validatorAccepts)
open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Address Datum Redeemer ScriptContext TxInfo TxInInfo TxOut Value validScriptContext lovelaceValue)

set_option warn.sorry false

-- structure OrderDatum where
--   owner : ByteString
--   amount : Int
--   policyId : ByteString
--   assetName : ByteString

-- def orderDatum (d : OrderDatum) : Data :=
--   Data.Constr 0
--   [ Data.B d.owner,
--     Data.I d.amount,
--     Data.B d.policyId,
--     Data.B d.assetName ]

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

def validOrder (utxo : TxOut) : Prop :=
  utxo.txOutAddress = ⟨.ScriptCredential "fake_script_hash_28bytes!!!!", none⟩

def validTransition (utxo contUtxo : TxOut) : Prop :=
  -- true
  contUtxo.txOutAddress = utxo.txOutAddress ∧
  contUtxo.txOutDatum = utxo.txOutDatum

def hasOutputs (ctx : ScriptContext) (outs : List TxOut) : Prop :=
  ctx.scriptContextTxInfo.txInfoOutputs = outs

def hasInputs (ctx : ScriptContext) (ins : List TxInInfo) : Prop :=
  ctx.scriptContextTxInfo.txInfoInputs = ins

def spend_sound_theorem (validator : Program) : Prop :=
    ∀ (inValue : Value) (outAddr : Address)
      (redeemer : Redeemer) (inDatum : Datum),
    let utxoRef := ⟨"txid_placeholder_32bytes!!!!!!!!", 0⟩
    let utxo : TxOut :=
      ⟨ ⟨.ScriptCredential "fake_script_hash_28bytes!!!!", none⟩,
        inValue,  -- NICE AND CHEAP
        .NoOutputDatum,   -- TODO: fix this
        none
      ⟩
    let someOutput : TxOut :=
      ⟨ outAddr,
        lovelaceValue 0,  -- TODO: fix this
        -- outValue,  -- THIS IS NOT CHEAP
        .NoOutputDatum,
        none
      ⟩
    let txInfo :=
      { baseTxInfo with
        txInfoInputs := [⟨utxoRef, utxo⟩]
        txInfoOutputs := [someOutput]
        -- txInfoRedeemers :=  -- TODO
      }
    let ctx : ScriptContext :=
      { scriptContextTxInfo := txInfo
        scriptContextRedeemer := redeemer -- FIXME
        -- scriptContextRedeemer := Data.Constr 0 [Data.I 0]
        scriptContextScriptInfo := .SpendingScript utxoRef (some inDatum)
      }
    -- XXX: this is returning false (but is not needed):
    -- validScriptContext ctx ∧
    -- hasInputs ctx [⟨utxoRef, utxo⟩] ∧  -- already covered
    validOrder utxo ∧
    validatorAccepts ctx validator →
    ∃ (contUtxo : TxOut),
      hasOutputs ctx [contUtxo] ∧
      validOrder someOutput ∧
      validTransition utxo someOutput

end Properties.Soundness
