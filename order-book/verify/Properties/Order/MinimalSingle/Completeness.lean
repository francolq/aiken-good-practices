import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Common
import Properties.Order.Common
import Properties.Order.Minimal.Spec

/-! Completeness for the minimal-single-input `order` validator. Same
    spec as `Minimal`, but the validator additionally requires exactly
    one input at the script's own address. -/

namespace Properties.Order.MinimalSingle.Completeness

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Program)
open Properties.Common (validatorAccepts)
open Properties.Order.Common (RedeemerKind)
open Properties.Order.Minimal.Spec

set_option warn.sorry false

#import_uplc orderMinimalSingleScript PlutusV3 flat_hex "Scripts/order_minimal_single_spend.flat"

def orderMinimalSingleValidator : Program := orderMinimalSingleScript.script

/-- Completeness of the `Resolve` branch. -/
theorem resolve_complete :
    ∀ (ownHash : ByteString) (input : ResolveInput) (cont : ResolveContinuation)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      wellFormedResolveValue cont.lovelace
                             input.datum.policyId input.datum.assetName cont.assetAmount →
      validResolve ownHash input cont →
      validatorAccepts
        (resolveCtx ownHash input cont (.Resolve 0)
                    fee validRange txId treasuryAmount treasuryDonation)
        orderMinimalSingleValidator
    := by blaster

/-- Completeness of the `Close` branch. -/
theorem close_complete :
    ∀ (ownHash : ByteString) (input : CloseInput) (signer : ByteString)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      validClose input signer →
      validatorAccepts
        (closeCtx ownHash input signer .Close
                  fee validRange txId treasuryAmount treasuryDonation)
        orderMinimalSingleValidator
    := by blaster

end Properties.Order.MinimalSingle.Completeness
