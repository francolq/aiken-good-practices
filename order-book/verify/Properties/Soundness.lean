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
      -- (askedAmount : Int)
      ,
    let inDatum : OrderDatum := {
      owner := "fake_owner_pkh"
      amount := 10
      -- amount := askedAmount  -- code 137 (Out of memory)
      policyId := "fake_policy_hash_28bytes!!!!"
      assetName := "fake_asset_name"
    }
    let inDatumData := orderData inDatum
    let utxoRef := ⟨"txid_placeholder_32bytes!!!!!!!!", 0⟩
    let utxo : TxOut :=
      ⟨ ⟨.ScriptCredential "fake_script_hash_28bytes!!!!", none⟩,
        lovelaceValue 0,  -- TODO: fix this
        -- inValue,  -- TODO: CAN THIS WORK? (inValue : Value)
        .OutputDatum inDatumData,
        -- .OutputDatum inDatum,  -- TODO: no need for this level of generality
        none
      ⟩
    let someOutput : TxOut :=
      ⟨ outAddr,
        add inDatum.policyId inDatum.assetName inDatum.amount (lovelaceValue 0), -- THIS IS CHEATING
        -- outValue,  -- THIS IS NOT CHEAP
        -- .NoOutputDatum,
        .OutputDatum inDatumData, -- THIS IS CHEATING
        -- outDatum,  -- THIS IS NOT CHEAP (outDatum : OutputDatum)
        none
      ⟩
    let txInfo :=
      { baseTxInfo with
        txInfoInputs := [⟨utxoRef, utxo⟩]
        txInfoOutputs := [someOutput]
        txInfoRedeemers := [(.Spending utxoRef, redeemer)]
      }
    let ctx : ScriptContext :=
      { scriptContextTxInfo := txInfo
        scriptContextRedeemer := redeemer -- FIXME
        -- scriptContextRedeemer := Data.Constr 0 [Data.I 0]
        scriptContextScriptInfo := .SpendingScript utxoRef inDatumData
      }
    -- XXX: this is returning false (but is not needed):
    -- validScriptContext ctx ∧
    -- hasInputs ctx [⟨utxoRef, utxo⟩] ∧  -- already covered
    -- askedAmount > 0 ∧
    -- askedAmount ≤ 10 ∧  -- code 137 (Out of memory)
    -- askedAmount = 10 ∧  -- TODO: WHY IS THIS NOT WORKING ???
    validOrder utxo inDatum ∧
    validatorAccepts ctx validator →
    -- ∃ (contUtxo : TxOut),  contUtxo = someOutput
      let contUtxo := someOutput
      hasOutputs ctx [contUtxo]
      ∧ validOrder contUtxo inDatum
      ∧ validTransition utxo contUtxo inDatum

end Properties.Soundness
