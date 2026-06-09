import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Order.Common
import Properties.Order.Vulnerable.Spec

/-! Completeness for the vulnerable validator's `Resolve` branch. -/

namespace Properties.Order.Vulnerable.Validator

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (Address ScriptContext TxOutRef)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Const Program)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)
open Properties.Order.Common (Datum ResolveInput ResolveContinuation
                              wellFormedResolveValue resolveCtx)
open Properties.Order.Vulnerable.Spec

set_option warn.sorry false

#import_uplc orderVulnerableScript PlutusV3 flat_hex "Scripts/order_vulnerable_spend.flat"

def orderVulnerableValidator : Program := orderVulnerableScript.script

def orderVulnerableAcceptsProp (ctx : ScriptContext) : Prop :=
  cekExecuteProgram orderVulnerableValidator [toTerm ctx] 5000000
    = .Halt (.VCon Const.Unit)

/-- Completeness of the vulnerable `Resolve` branch. -/
theorem resolve_complete :
    ∀ (ownHash : ByteString) (input : ResolveInput) (cont : ResolveContinuation)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      wellFormedResolveValue cont.lovelace ownHash cont.valQty
                             input.datum.policyId input.datum.assetName cont.assetAmount →
      validResolve ownHash input cont →
      orderVulnerableAcceptsProp
        (resolveCtx ownHash input cont
                    fee validRange txId treasuryAmount treasuryDonation)
    := by blaster

end Properties.Order.Vulnerable.Validator
