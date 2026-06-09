import Properties.Order.Common

/-! Pure Lean specification for the complete `order` validator.

    Anti-double-satisfaction strategy: the `Resolve` branch updates the
    continuation datum's `tag` field to the current `own_ref`, binding
    the produced continuation to the input being spent. -/

namespace Properties.Order.Complete.Spec

open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.V3 (Address Credential TxOutRef)
open Properties.Order.Common (CloseInput CloseMint MintAction MintOutput
                              ResolveInput ResolveContinuation scriptAddr)

/-- Resolve spec: the continuation lives at the script's own address,
    preserves or increases the input's lovelace, carries exactly one
    `val` token, holds at least `amount` of the requested asset, and
    propagates the input datum with `tag := some input.ref`. -/
def validResolve (ownHash : ByteString)
    (input : ResolveInput) (cont : ResolveContinuation) : Prop :=
  cont.address = scriptAddr ownHash ∧
  input.lovelace ≤ cont.lovelace ∧
  cont.valQty = 1 ∧
  cont.assetAmount ≥ input.datum.amount ∧
  cont.datum = { input.datum with tag := some input.ref }

/-- Close spec: the signer matches the input datum's owner, the burn
    happens under the script's own policy, the asset name is `"val"`,
    and the burnt quantity is strictly negative. -/
def validClose (ownHash : ByteString) (input : CloseInput)
    (signer : ByteString) (mint : CloseMint) : Prop :=
  signer = input.datum.owner ∧
  mint.policy = ownHash ∧
  mint.assetName = "val" ∧
  mint.burnedQty < 0

/-- Mint spec: the order output sits at an address whose payment
    credential is `Script mint.policyId`, carries exactly one
    `(policyId, "val")` unit, the total minted quantity is exactly one,
    and the initial datum's `tag` is `none`. -/
def validMint (mint : MintAction) (output : MintOutput) : Prop :=
  output.address.addressCredential = Credential.ScriptCredential mint.policyId ∧
  output.valQty = 1 ∧
  mint.mintedQty = 1 ∧
  output.tag = none

/-- Burn spec: the minted quantity is strictly negative. -/
def validBurn (burnedQty : Int) : Prop := burnedQty < 0

end Properties.Order.Complete.Spec
