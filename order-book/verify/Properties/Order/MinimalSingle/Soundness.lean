import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Order.Common
import Properties.Order.Minimal.Spec
import Properties.Order.Minimal.Completeness
import Properties.Order.MinimalSingle.Completeness

/-! Soundness for the minimal-single-input `order` validator. -/

namespace Properties.Order.MinimalSingle.Soundness

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open Properties.Order.Common (RedeemerKind)
open Properties.Order.Minimal.Spec
open Properties.Order.Minimal.Completeness (closeCtx resolveCtx)
open Properties.Order.MinimalSingle.Completeness (orderMinimalSingleAcceptsProp)

set_option warn.sorry false

/-- The minimal-single-input validator's `Resolve` branch is *unsound*:
    the single-input restriction only blocks double-satisfaction; it
    does not constrain the continuation's address or datum, so the
    property in `Spec.validResolve` does not follow from acceptance. -/
theorem resolve_unsound :
    ¬ (∀ (ownHash : ByteString) (input : ResolveInput) (cont : ResolveContinuation)
        (r : RedeemerKind)
        (fee : Int) (validRange : Data) (txId : ByteString)
        (treasuryAmount treasuryDonation : Data),
        wellFormedResolveValue cont.lovelace
                               input.datum.policyId input.datum.assetName cont.assetAmount →
        orderMinimalSingleAcceptsProp
          (resolveCtx ownHash input cont r
                      fee validRange txId treasuryAmount treasuryDonation) →
        validResolve ownHash input cont)
    := by blaster

/-- Soundness of the `Close` branch. -/
theorem close_sound :
    ∀ (ownHash : ByteString) (input : CloseInput) (signer : ByteString)
      (r : RedeemerKind)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      orderMinimalSingleAcceptsProp
        (closeCtx ownHash input signer r
                  fee validRange txId treasuryAmount treasuryDonation) →
      validClose input signer
    := by blaster

end Properties.Order.MinimalSingle.Soundness
