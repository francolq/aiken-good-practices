import Properties.Order.Common

/-! Pure Lean specification for the vulnerable `order` validator.

    The vulnerable variant fails to bind the continuation to the input:
    its `Resolve` branch checks `tag = none` instead of `tag = some own_ref`,
    leaving the validator open to double-satisfaction attacks. -/

namespace Properties.Order.Vulnerable.Spec

open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.V3 (Address TxOutRef)
open Properties.Order.Common (Datum ResolveInput ResolveContinuation scriptAddr)

/-- Resolve spec for the vulnerable validator. Same shape as the complete
    spec except the continuation datum carries `tag := none`, which
    fails to bind the continuation to the spent input. -/
def validResolve (ownHash : ByteString)
    (input : ResolveInput) (cont : ResolveContinuation) : Prop :=
  cont.address = scriptAddr ownHash ∧
  input.value.lovelace ≤ cont.lovelace ∧
  cont.valQty = 1 ∧
  cont.assetAmount ≥ input.datum.amount ∧
  cont.datum = { input.datum with tag := none }

end Properties.Order.Vulnerable.Spec
