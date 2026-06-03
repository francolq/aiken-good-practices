import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Order.Spec
import Properties.Order.Validator
import Properties.Order.MintValidator

/-! Soundness for the compiled `order` validator: under the Value's
    well-formedness invariant, acceptance implies the spec predicate.
    Combined with `Properties.Order.Validator.resolve_complete`, this
    yields `wellFormed → (validResolve ↔ accept)` for `Resolve`. -/

namespace Properties.Order.Soundness

open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.V3 (Address Credential TxOutRef)
open Properties.Order.Spec
open Properties.Order.Validator (closeCtx orderAcceptsProp resolveCtx)
open Properties.Order.MintValidator (burnCtx mintCtxMint orderMintAcceptsProp)

set_option warn.sorry false

/-- Soundness of the `Resolve` branch. -/
theorem resolve_sound :
    ∀ (ownHash : ByteString) (inDatum contDatum : Datum)
      (ownRef : TxOutRef) (contAddr : Address)
      (inLovelace contLovelace : Int)
      (contValQty contAssetAmount : Int),
      wellFormedResolveValue contLovelace ownHash contValQty
                             inDatum.policyId inDatum.assetName contAssetAmount →
      orderAcceptsProp
        (resolveCtx ownHash inDatum contDatum ownRef contAddr
                    inLovelace contLovelace contValQty contAssetAmount) →
      validResolve ownHash inDatum contDatum ownRef contAddr
                   inLovelace contLovelace contValQty contAssetAmount
    := by blaster

/-- Soundness of the `Close` branch. -/
theorem close_sound :
    ∀ (ownHash owner : ByteString) (ownRef : TxOutRef) (signer : ByteString)
      (mintPolicy mintAssetName : ByteString) (burnedQty : Int),
      orderAcceptsProp
        (closeCtx ownHash owner ownRef signer
                  mintPolicy mintAssetName burnedQty) →
      validClose ownHash owner signer mintPolicy mintAssetName burnedQty
    := by blaster

/-- Soundness of the `Mint` branch. -/
theorem mint_sound :
    ∀ (policyId : ByteString) (orderAddr : Address)
      (orderValQty mintedQty : Int) (tag : Option TxOutRef),
      orderMintAcceptsProp
        (mintCtxMint policyId orderAddr orderValQty mintedQty tag) →
      validMint policyId orderAddr orderValQty mintedQty tag
    := by blaster

/-- Soundness of the `Burn` branch. -/
theorem burn_sound :
    ∀ (policyId : ByteString) (burnedQty : Int),
      orderMintAcceptsProp (burnCtx policyId burnedQty) →
      validBurn burnedQty
    := by blaster

end Properties.Order.Soundness
