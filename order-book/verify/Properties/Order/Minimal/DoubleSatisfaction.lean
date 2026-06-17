import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Common
import Properties.Order.Common
import Properties.Order.Minimal.Spec
import Properties.Order.Minimal.Completeness

/-! Double-satisfaction for the minimal validator. -/

namespace Properties.Order.Minimal.DoubleSatisfaction

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open CardanoLedgerApi.V3 (Address ScriptContext ScriptPurpose TxOut TxOutRef)
open Properties.Common (validatorAccepts)
open Properties.Order.Common (InputValue RedeemerKind redeemerKindData scriptAddr inputValueToValue)
open Properties.Order.Minimal.Spec
open Properties.Order.Minimal.Completeness (orderMinimalValidator)

set_option warn.sorry false

structure DSInputs where
  datum  : OrderDatum
  ref1   : TxOutRef
  ref2   : TxOutRef
  value1 : InputValue
  value2 : InputValue

structure DSContinuation where
  datum       : OrderDatum
  lovelace    : Int
  assetAmount : Int

def doubleInputCtx
    (ownHash : ByteString)
    (inputs : DSInputs) (cont : DSContinuation)
    (ownRef : TxOutRef) (redeemer : RedeemerKind)
    (fee : Int) (validRange : Data) (txId : ByteString)
    (treasuryAmount treasuryDonation : Data) : ScriptContext :=
  let ownAddr := scriptAddr ownHash
  let inDatumD := datumData inputs.datum
  let in1 : TxOut :=
    ⟨ownAddr, inputValueToValue inputs.value1, .OutputDatum inDatumD, none⟩
  let in2 : TxOut :=
    ⟨ownAddr, inputValueToValue inputs.value2, .OutputDatum inDatumD, none⟩
  let contValue :=
    twoEntryValue cont.lovelace
                  inputs.datum.policyId inputs.datum.assetName cont.assetAmount
  let contOutput : TxOut :=
    ⟨ownAddr, contValue, .OutputDatum (datumData cont.datum), none⟩
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨inputs.ref1, in1⟩, ⟨inputs.ref2, in2⟩]
        txInfoReferenceInputs := []
        txInfoOutputs := [contOutput]
        txInfoFee := fee
        txInfoMint := []
        txInfoTxCerts := []
        txInfoWdrl := []
        txInfoValidRange := validRange
        txInfoSignatories := []
        txInfoRedeemers :=
          [(ScriptPurpose.Spending inputs.ref1, redeemerKindData redeemer),
           (ScriptPurpose.Spending inputs.ref2, redeemerKindData redeemer)]
        txInfoData := []
        txInfoId := txId
        txInfoVotes := []
        txInfoProposalProcedures := []
        txInfoCurrentTreasuryAmount := treasuryAmount
        txInfoTreasuryDonation := treasuryDonation
      }
    scriptContextRedeemer := redeemerKindData redeemer
    scriptContextScriptInfo :=
      .SpendingScript ownRef (some (datumData inputs.datum))
  }

def noDoubleSatisfaction (acceptsProp : ScriptContext → Prop) : Prop :=
  ∀ (ownHash : ByteString) (inDatum contDatum : OrderDatum)
    (ref1 ref2 : TxOutRef)
    (value1 value2 : InputValue)
    (contLovelace contAssetAmount : Int)
    (redeemer : RedeemerKind)
    (fee : Int) (validRange : Data) (txId : ByteString)
    (treasuryAmount treasuryDonation : Data),
    ref1 ≠ ref2 →
    let inputs : DSInputs := ⟨inDatum, ref1, ref2, value1, value2⟩
    let cont   : DSContinuation := ⟨contDatum, contLovelace, contAssetAmount⟩
    ¬ (acceptsProp
          (doubleInputCtx ownHash inputs cont ref1 redeemer
                          fee validRange txId treasuryAmount treasuryDonation)
     ∧ acceptsProp
          (doubleInputCtx ownHash inputs cont ref2 redeemer
                          fee validRange txId treasuryAmount treasuryDonation))

theorem no_double_satisfaction_fails :
    ¬ noDoubleSatisfaction (validatorAccepts · orderMinimalValidator)
    := by blaster

end Properties.Order.Minimal.DoubleSatisfaction
