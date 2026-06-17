import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Common
import Properties.Order.Common
import Properties.Order.Complete.Spec
import Properties.Order.Complete.Completeness
import Properties.Order.Complete.MintCompleteness

/-! Soundness for the compiled complete `order` validator. Under the
    Value's well-formedness invariant, acceptance implies the spec
    predicate. Combined with `resolve_complete`, this yields
    `wellFormed → (validResolve ↔ accept)` for `Resolve`. -/

namespace Properties.Order.Complete.Soundness

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open CardanoLedgerApi.V3 (Address Credential TxOutRef)
open Properties.Common (validatorAccepts)
open Properties.Order.Common (RedeemerKind)
open Properties.Order.Complete.Spec
open Properties.Order.Complete.Completeness (closeCtx orderValidator)
open Properties.Order.Complete.MintCompleteness (burnCtx mintCtxMint orderMintValidator)

set_option warn.sorry false

/-- Soundness of the `Resolve` branch. -/
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
        orderValidator →
      validResolve ownHash input cont
    := by blaster

/-- Soundness of the `Close` branch. -/
theorem close_sound :
    ∀ (ownHash : ByteString) (input : CloseInput) (signer : ByteString)
      (mint : CloseMint) (mintRedeemer : Data)
      (r : RedeemerKind)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      validatorAccepts
        (closeCtx ownHash input signer mint mintRedeemer r
                  fee validRange txId treasuryAmount treasuryDonation)
        orderValidator →
      validClose ownHash input signer mint
    := by blaster

/-- Soundness of the `Mint` branch. -/
theorem mint_sound :
    ∀ (mint : MintAction) (output : MintOutput)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      validatorAccepts
        (mintCtxMint mint output
                     fee validRange txId treasuryAmount treasuryDonation)
        orderMintValidator →
      validMint mint output
    := by blaster

/-- Soundness of the `Burn` branch. -/
theorem burn_sound :
    ∀ (policyId : ByteString) (burnedQty : Int)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      validatorAccepts
        (burnCtx policyId burnedQty
                 fee validRange txId treasuryAmount treasuryDonation)
        orderMintValidator →
      validBurn burnedQty
    := by blaster

end Properties.Order.Complete.Soundness
