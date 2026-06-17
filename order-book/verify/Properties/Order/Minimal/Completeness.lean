import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Order.Common
import Properties.Order.Minimal.Spec

/-! Completeness theorems and execution wrappers for the compiled
    minimal `order` spending validator. -/

namespace Properties.Order.Minimal.Completeness

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (Address OutputDatum ScriptContext ScriptPurpose TxInInfo TxOut
                          TxOutRef)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Const Program)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)
open Properties.Order.Common (RedeemerKind scriptAddr redeemerKindData inputValueToValue)
open Properties.Order.Minimal.Spec

set_option warn.sorry false

#import_uplc orderMinimalScript PlutusV3 flat_hex "Scripts/order_minimal_spend.flat"

def orderMinimalValidator : Program := orderMinimalScript.script

def orderMinimalAcceptsProp (ctx : ScriptContext) : Prop :=
  cekExecuteProgram orderMinimalValidator [toTerm ctx] 5000000
    = .Halt (.VCon Const.Unit)

/-- `ScriptContext` for a `Resolve`-style transaction, parametric in
    the spend redeemer `r`. -/
def resolveCtx
    (ownHash : ByteString)
    (input : ResolveInput) (cont : ResolveContinuation)
    (r : RedeemerKind)
    (fee : Int) (validRange : Data) (txId : ByteString)
    (treasuryAmount treasuryDonation : Data) : ScriptContext :=
  let ownAddr := scriptAddr ownHash
  let inResolved : TxOut :=
    ⟨ownAddr, inputValueToValue input.value,
     .OutputDatum (datumData input.datum), none⟩
  let contValue :=
    twoEntryValue cont.lovelace
                  input.datum.policyId input.datum.assetName cont.assetAmount
  let contOutput : TxOut :=
    ⟨cont.address, contValue, .OutputDatum (datumData cont.datum), none⟩
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨input.ref, inResolved⟩]
        txInfoReferenceInputs := []
        txInfoOutputs := [contOutput]
        txInfoFee := fee
        txInfoMint := []
        txInfoTxCerts := []
        txInfoWdrl := []
        txInfoValidRange := validRange
        txInfoSignatories := []
        txInfoRedeemers :=
          [(ScriptPurpose.Spending input.ref, redeemerKindData r)]
        txInfoData := []
        txInfoId := txId
        txInfoVotes := []
        txInfoProposalProcedures := []
        txInfoCurrentTreasuryAmount := treasuryAmount
        txInfoTreasuryDonation := treasuryDonation
      }
    scriptContextRedeemer := redeemerKindData r
    scriptContextScriptInfo :=
      .SpendingScript input.ref (some (datumData input.datum))
  }

/-- `ScriptContext` for a `Close`-style transaction, parametric in
    the spend redeemer `r`. -/
def closeCtx
    (ownHash : ByteString)
    (input : CloseInput) (signer : ByteString)
    (r : RedeemerKind)
    (fee : Int) (validRange : Data) (txId : ByteString)
    (treasuryAmount treasuryDonation : Data) : ScriptContext :=
  let ownAddr := scriptAddr ownHash
  let inResolved : TxOut :=
    ⟨ownAddr, inputValueToValue input.value,
     .OutputDatum (datumData input.datum), none⟩
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨input.ref, inResolved⟩]
        txInfoReferenceInputs := []
        txInfoOutputs := []
        txInfoFee := fee
        txInfoMint := []
        txInfoTxCerts := []
        txInfoWdrl := []
        txInfoValidRange := validRange
        txInfoSignatories := [signer]
        txInfoRedeemers :=
          [(ScriptPurpose.Spending input.ref, redeemerKindData r)]
        txInfoData := []
        txInfoId := txId
        txInfoVotes := []
        txInfoProposalProcedures := []
        txInfoCurrentTreasuryAmount := treasuryAmount
        txInfoTreasuryDonation := treasuryDonation
      }
    scriptContextRedeemer := redeemerKindData r
    scriptContextScriptInfo :=
      .SpendingScript input.ref (some (datumData input.datum))
  }

/-- Completeness of the `Resolve` branch. -/
theorem resolve_complete :
    ∀ (ownHash : ByteString) (input : ResolveInput) (cont : ResolveContinuation)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      wellFormedResolveValue cont.lovelace
                             input.datum.policyId input.datum.assetName cont.assetAmount →
      validResolve ownHash input cont →
      orderMinimalAcceptsProp
        (resolveCtx ownHash input cont (.Resolve 0)
                    fee validRange txId treasuryAmount treasuryDonation)
    := by blaster

/-- Completeness of the `Close` branch. -/
theorem close_complete :
    ∀ (ownHash : ByteString) (input : CloseInput) (signer : ByteString)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      validClose input signer →
      orderMinimalAcceptsProp
        (closeCtx ownHash input signer .Close
                  fee validRange txId treasuryAmount treasuryDonation)
    := by blaster

end Properties.Order.Minimal.Completeness
