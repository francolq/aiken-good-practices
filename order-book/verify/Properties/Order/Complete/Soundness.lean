import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Order.Common
import Properties.Order.Complete.Spec
import Properties.Order.Complete.Validator
import Properties.Order.Complete.MintValidator

/-! Soundness for the compiled complete `order` validator. Under the
    Value's well-formedness invariant, acceptance implies the spec
    predicate. Combined with `resolve_complete`, this yields
    `wellFormed → (validResolve ↔ accept)` for `Resolve`. -/

namespace Properties.Order.Complete.Soundness

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open CardanoLedgerApi.V3 (Address Credential TxOutRef)
open Properties.Order.Common (CloseInput CloseMint MintAction MintOutput
                              ResolveInput ResolveContinuation
                              wellFormedResolveValue resolveCtx)
open Properties.Order.Complete.Spec
open Properties.Order.Complete.Validator (closeCtx orderAcceptsProp)
open Properties.Order.Complete.MintValidator (burnCtx mintCtxMint orderMintAcceptsProp)

set_option warn.sorry false

/-- Soundness of the `Resolve` branch. -/
theorem resolve_sound :
    ∀ (ownHash : ByteString) (input : ResolveInput) (cont : ResolveContinuation)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      wellFormedResolveValue cont.lovelace ownHash cont.valQty
                             input.datum.policyId input.datum.assetName cont.assetAmount →
      orderAcceptsProp
        (resolveCtx ownHash input cont
                    fee validRange txId treasuryAmount treasuryDonation) →
      validResolve ownHash input cont
    := by blaster

/-- Soundness of the `Close` branch. -/
theorem close_sound :
    ∀ (ownHash : ByteString) (input : CloseInput) (signer : ByteString)
      (mint : CloseMint) (mintRedeemer : Data)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      orderAcceptsProp
        (closeCtx ownHash input signer mint mintRedeemer
                  fee validRange txId treasuryAmount treasuryDonation) →
      validClose ownHash input signer mint
    := by blaster

/-- Soundness of the `Mint` branch. -/
theorem mint_sound :
    ∀ (mint : MintAction) (output : MintOutput)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      orderMintAcceptsProp
        (mintCtxMint mint output
                     fee validRange txId treasuryAmount treasuryDonation) →
      validMint mint output
    := by blaster

/-- Soundness of the `Burn` branch. -/
theorem burn_sound :
    ∀ (policyId : ByteString) (burnedQty : Int)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      orderMintAcceptsProp
        (burnCtx policyId burnedQty
                 fee validRange txId treasuryAmount treasuryDonation) →
      validBurn burnedQty
    := by blaster

end Properties.Order.Complete.Soundness
