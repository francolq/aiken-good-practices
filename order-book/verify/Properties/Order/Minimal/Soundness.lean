import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Common
import Properties.Order.Common
import Properties.Order.Minimal.Spec
import Properties.Order.Minimal.Completeness

/-! Soundness for the compiled minimal `order` validator. -/

namespace Properties.Order.Minimal.Soundness

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open Properties.Common (validatorAccepts)
open Properties.Order.Common (RedeemerKind)
open Properties.Order.Minimal.Spec
open Properties.Order.Minimal.Completeness (closeCtx orderMinimalValidator resolveCtx)

set_option warn.sorry false

/-- The minimal validator's `Resolve` branch is *unsound*: it accepts
    transactions whose continuation breaks the address or datum
    constraint, so the property in `Spec.validResolve` does not follow
    from acceptance. -/
theorem resolve_unsound :
    ¬ (∀ (ownHash : ByteString) (input : ResolveInput) (cont : ResolveContinuation)
        (r : RedeemerKind)
        (fee : Int) (validRange : Data) (txId : ByteString)
        (treasuryAmount treasuryDonation : Data),
        wellFormedResolveValue cont.lovelace
                               input.datum.policyId input.datum.assetName cont.assetAmount →
        validatorAccepts
          (resolveCtx ownHash input cont r
                      fee validRange txId treasuryAmount treasuryDonation)
          orderMinimalValidator →
        validResolve ownHash input cont)
    := by blaster

/-- Soundness of the `Close` branch. -/
theorem close_sound :
    ∀ (ownHash : ByteString) (input : CloseInput) (signer : ByteString)
      (r : RedeemerKind)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      validatorAccepts
        (closeCtx ownHash input signer r
                  fee validRange txId treasuryAmount treasuryDonation)
        orderMinimalValidator →
      validClose input signer
    := by blaster

end Properties.Order.Minimal.Soundness
