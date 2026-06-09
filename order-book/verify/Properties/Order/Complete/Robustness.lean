import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Order.Common
import Properties.Order.Complete.Spec

/-! Robustness theorems for the complete validator: each violation
    hypothesis falsifies the spec. Combined with soundness, this gives
    `H → ¬ accepts` as a corollary. -/

namespace Properties.Order.Complete.Robustness

open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.V3 (Address Credential TxOutRef)
open Properties.Order.Common (CloseInput CloseMint MintAction MintOutput
                              ResolveInput ResolveContinuation scriptAddr)
open Properties.Order.Complete.Spec

set_option warn.sorry false

/-! ## Resolve-branch robustness -/

/-- A continuation at the wrong address violates `validResolve`. -/
theorem resolve_wrong_address_invalidates_spec :
    ∀ (ownHash : ByteString) (input : ResolveInput) (cont : ResolveContinuation),
      cont.address ≠ scriptAddr ownHash →
      ¬ validResolve ownHash input cont
    := by blaster

/-- A continuation that loses lovelace violates `validResolve`. -/
theorem resolve_value_loss_invalidates_spec :
    ∀ (ownHash : ByteString) (input : ResolveInput) (cont : ResolveContinuation),
      cont.lovelace < input.lovelace →
      ¬ validResolve ownHash input cont
    := by blaster

/-- The continuation datum must equal `{ input.datum with tag := some input.ref }`
    (anti-double-satisfaction invariant). -/
theorem resolve_datum_change_invalidates_spec :
    ∀ (ownHash : ByteString) (input : ResolveInput) (cont : ResolveContinuation),
      cont.datum ≠ { input.datum with tag := some input.ref } →
      ¬ validResolve ownHash input cont
    := by blaster

/-! ## Close-branch robustness -/

/-- The transaction signer must equal the input datum's owner. -/
theorem close_wrong_signer_invalidates_spec :
    ∀ (ownHash : ByteString) (input : CloseInput) (signer : ByteString)
      (mint : CloseMint),
      signer ≠ input.datum.owner →
      ¬ validClose ownHash input signer mint
    := by blaster

/-- The burn must happen under the script's own policy. -/
theorem close_wrong_mint_policy_invalidates_spec :
    ∀ (ownHash : ByteString) (input : CloseInput) (signer : ByteString)
      (mint : CloseMint),
      mint.policy ≠ ownHash →
      ¬ validClose ownHash input signer mint
    := by blaster

/-- The burnt asset must be literally `"val"`. -/
theorem close_wrong_mint_asset_invalidates_spec :
    ∀ (ownHash : ByteString) (input : CloseInput) (signer : ByteString)
      (mint : CloseMint),
      mint.assetName ≠ "val" →
      ¬ validClose ownHash input signer mint
    := by blaster

/-- The burnt quantity must be strictly negative. -/
theorem close_nonneg_qty_invalidates_spec :
    ∀ (ownHash : ByteString) (input : CloseInput) (signer : ByteString)
      (mint : CloseMint),
      mint.burnedQty ≥ 0 →
      ¬ validClose ownHash input signer mint
    := by blaster

/-! ## Mint-branch robustness -/

/-- The order output must sit at an address whose payment credential
    is `Script mint.policyId`. -/
theorem mint_wrong_address_invalidates_spec :
    ∀ (mint : MintAction) (output : MintOutput),
      output.address.addressCredential ≠ Credential.ScriptCredential mint.policyId →
      ¬ validMint mint output
    := by blaster

/-- The order output must carry exactly one `(policyId, "val")` unit. -/
theorem mint_wrong_val_qty_invalidates_spec :
    ∀ (mint : MintAction) (output : MintOutput),
      output.valQty ≠ 1 →
      ¬ validMint mint output
    := by blaster

/-- The total minted quantity of `(policyId, "val")` must be exactly 1. -/
theorem mint_wrong_mint_qty_invalidates_spec :
    ∀ (mint : MintAction) (output : MintOutput),
      mint.mintedQty ≠ 1 →
      ¬ validMint mint output
    := by blaster

end Properties.Order.Complete.Robustness
