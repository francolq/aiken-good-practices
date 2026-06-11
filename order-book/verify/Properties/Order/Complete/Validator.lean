import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Order.Common
import Properties.Order.Complete.Spec

/-! Completeness theorems and execution wrappers for the compiled
    complete `order` spending validator. -/

namespace Properties.Order.Complete.Validator

open CardanoLedgerApi.IsData.Class (IsData toTerm)
open CardanoLedgerApi.V3 (Address OutputDatum ScriptContext ScriptPurpose TxInInfo TxOut
                          TxOutRef lovelaceValue singleton)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Const Program)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)
open Properties.Order.Common (CloseInput CloseMint RedeemerKind ResolveInput ResolveContinuation
                              scriptAddr wellFormedResolveValue
                              orderDatumData redeemerKindData resolveCtx)
open Properties.Order.Complete.Spec

set_option warn.sorry false

#import_uplc orderScript PlutusV3 flat_hex "Scripts/order_spend.flat"

def orderValidator : Program := orderScript.script

def orderAcceptsProp (ctx : ScriptContext) : Prop :=
  cekExecuteProgram orderValidator [toTerm ctx] 5000000
    = .Halt (.VCon Const.Unit)

/-- `ScriptContext` for a `Close`-style transaction. -/
def closeCtx
    (ownHash : ByteString)
    (input : CloseInput) (signer : ByteString)
    (mint : CloseMint) (mintRedeemer : Data)
    (r : RedeemerKind)
    (fee : Int) (validRange : Data) (txId : ByteString)
    (treasuryAmount treasuryDonation : Data) : ScriptContext :=
  let ownAddr := scriptAddr ownHash
  let inResolved : TxOut :=
    ⟨ownAddr, lovelaceValue 0,
     .OutputDatum (orderDatumData input.datum), none⟩
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨input.ref, inResolved⟩]
        txInfoReferenceInputs := []
        txInfoOutputs := []
        txInfoFee := fee
        txInfoMint := singleton mint.policy mint.assetName mint.burnedQty
        txInfoTxCerts := []
        txInfoWdrl := []
        txInfoValidRange := validRange
        txInfoSignatories := [signer]
        txInfoRedeemers :=
          [(ScriptPurpose.Spending input.ref, redeemerKindData r),
           (ScriptPurpose.Minting mint.policy, mintRedeemer)]
        txInfoData := []
        txInfoId := txId
        txInfoVotes := []
        txInfoProposalProcedures := []
        txInfoCurrentTreasuryAmount := treasuryAmount
        txInfoTreasuryDonation := treasuryDonation
      }
    scriptContextRedeemer := redeemerKindData r
    scriptContextScriptInfo :=
      .SpendingScript input.ref (some (orderDatumData input.datum))
  }

/-- Completeness of the `Resolve` branch. -/
theorem resolve_complete :
    ∀ (ownHash : ByteString) (input : ResolveInput) (cont : ResolveContinuation)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      wellFormedResolveValue cont.lovelace ownHash cont.valQty
                             input.datum.policyId input.datum.assetName cont.assetAmount →
      validResolve ownHash input cont →
      orderAcceptsProp
        (resolveCtx ownHash input cont (.Resolve 0)
                    fee validRange txId treasuryAmount treasuryDonation)
    := by blaster

/-- Completeness of the `Close` branch. -/
theorem close_complete :
    ∀ (ownHash : ByteString) (input : CloseInput) (signer : ByteString)
      (mint : CloseMint) (mintRedeemer : Data)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      validClose ownHash input signer mint →
      orderAcceptsProp
        (closeCtx ownHash input signer mint mintRedeemer .Close
                  fee validRange txId treasuryAmount treasuryDonation)
    := by blaster

end Properties.Order.Complete.Validator
