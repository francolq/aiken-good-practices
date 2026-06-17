import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Common
import Properties.Order.Common
import Properties.Order.Complete.Spec
import Properties.Order.Vulnerable.Spec
import Properties.Order.Vulnerable.Completeness

/-! Soundness for the compiled vulnerable validator's `Resolve` branch. -/

namespace Properties.Order.Vulnerable.Soundness

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open CardanoLedgerApi.V3 (Address TxOutRef)
open Properties.Common (validatorAccepts)
open Properties.Order.Common (RedeemerKind)
open Properties.Order.Complete.Spec (OrderDatum ResolveInput ResolveContinuation
                                     wellFormedResolveValue resolveCtx)
open Properties.Order.Vulnerable.Spec
open Properties.Order.Vulnerable.Completeness (orderVulnerableValidator)

set_option warn.sorry false

/-- Soundness of the vulnerable `Resolve` branch. -/
theorem resolve_sound :
    ∀ (ownHash : ByteString) (input : ResolveInput) (cont : ResolveContinuation)
      (r : RedeemerKind)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      wellFormedResolveValue cont.lovelace ownHash cont.valQty
                             input.datum.policyId input.datum.assetName cont.assetAmount →
      validatorAccepts
        (resolveCtx ownHash input cont r
                    fee validRange txId treasuryAmount treasuryDonation)
        orderVulnerableValidator →
      validResolve ownHash input cont
    := by blaster

end Properties.Order.Vulnerable.Soundness
