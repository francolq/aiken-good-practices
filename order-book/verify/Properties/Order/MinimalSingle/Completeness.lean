import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Order.Common
import Properties.Order.Minimal.Spec
import Properties.Order.Minimal.Completeness

/-! Completeness for the minimal-single-input `order` validator. Same
    spec as `Minimal`, but the validator additionally requires exactly
    one input at the script's own address. -/

namespace Properties.Order.MinimalSingle.Completeness

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Const Program)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)
open Properties.Order.Common (RedeemerKind)
open Properties.Order.Minimal.Spec
open Properties.Order.Minimal.Completeness (closeCtx resolveCtx)

set_option warn.sorry false

#import_uplc orderMinimalSingleScript PlutusV3 flat_hex "Scripts/order_minimal_single_spend.flat"

def orderMinimalSingleValidator : Program := orderMinimalSingleScript.script

def orderMinimalSingleAcceptsProp (ctx : ScriptContext) : Prop :=
  cekExecuteProgram orderMinimalSingleValidator [toTerm ctx] 5000000
    = .Halt (.VCon Const.Unit)

/-- Completeness of the `Resolve` branch. -/
theorem resolve_complete :
    ∀ (ownHash : ByteString) (input : ResolveInput) (cont : ResolveContinuation)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      wellFormedResolveValue cont.lovelace
                             input.datum.policyId input.datum.assetName cont.assetAmount →
      validResolve ownHash input cont →
      orderMinimalSingleAcceptsProp
        (resolveCtx ownHash input cont (.Resolve 0)
                    fee validRange txId treasuryAmount treasuryDonation)
    := by blaster

/-- Completeness of the `Close` branch. -/
theorem close_complete :
    ∀ (ownHash : ByteString) (input : CloseInput) (signer : ByteString)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      validClose input signer →
      orderMinimalSingleAcceptsProp
        (closeCtx ownHash input signer .Close
                  fee validRange txId treasuryAmount treasuryDonation)
    := by blaster

end Properties.Order.MinimalSingle.Completeness
