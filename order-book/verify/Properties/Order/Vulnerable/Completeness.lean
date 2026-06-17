import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Common
import Properties.Order.Common
import Properties.Order.Complete.Spec
import Properties.Order.Vulnerable.Spec

/-! Completeness for the vulnerable validator's `Resolve` branch. -/

namespace Properties.Order.Vulnerable.Completeness

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Program)
open Properties.Common (validatorAccepts)
open Properties.Order.Complete.Spec (OrderDatum ResolveInput ResolveContinuation
                                     wellFormedResolveValue resolveCtx)
open Properties.Order.Vulnerable.Spec

set_option warn.sorry false

#import_uplc orderVulnerableScript PlutusV3 flat_hex "Scripts/order_vulnerable_spend.flat"

def orderVulnerableValidator : Program := orderVulnerableScript.script

/-- Completeness of the vulnerable `Resolve` branch. -/
theorem resolve_complete :
    ∀ (ownHash : ByteString) (input : ResolveInput) (cont : ResolveContinuation)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      wellFormedResolveValue cont.lovelace ownHash cont.valQty
                             input.datum.policyId input.datum.assetName cont.assetAmount →
      validResolve ownHash input cont →
      validatorAccepts
        (resolveCtx ownHash input cont (.Resolve 0)
                    fee validRange txId treasuryAmount treasuryDonation)
        orderVulnerableValidator
    := by blaster

end Properties.Order.Vulnerable.Completeness
