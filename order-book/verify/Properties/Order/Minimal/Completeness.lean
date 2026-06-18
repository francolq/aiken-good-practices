import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Common
import Properties.Order.Common
import Properties.Order.Minimal.Spec

/-! Completeness theorems and execution wrappers for the compiled
    minimal `order` spending validator. -/

namespace Properties.Order.Minimal.Completeness

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Program)
open Properties.Common (validatorAccepts)
open Properties.Order.Common (RedeemerKind)
open Properties.Order.Minimal.Spec

set_option warn.sorry false

#import_uplc orderMinimalScript PlutusV3 flat_hex "Scripts/order_minimal_spend.flat"

def orderMinimalValidator : Program := orderMinimalScript.script

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
        orderMinimalValidator
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
        orderMinimalValidator
    := by blaster

end Properties.Order.Minimal.Completeness
