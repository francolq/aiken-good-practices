import CardanoLedgerApi.V3
import CardanoLedgerApi.V1.Contexts

/-! Pure Lean specification for the `order` validator

    Anti-double-satisfaction strategy: the `Resolve` branch updates
    the continuation datum's `tag` field to the current `own_ref`,
    binding the produced continuation to the input being spent. -/

namespace Properties.Order.Spec

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open CardanoLedgerApi.V3 (Address Credential CurrencySymbol TokenName TxOutRef Value)

structure Datum where
  owner : ByteString
  amount : Int
  policyId : ByteString
  assetName : ByteString
  tag : Option TxOutRef

def scriptAddr (h : ByteString) : Address :=
  { addressCredential := .ScriptCredential h
    addressStakingCredential := none }

/-! ## Helper functions -/

/-- Continuation value: exactly three entries (ada, `val` under
    `ownHash`, requested asset under `(policyId, assetName)`). Mirrors
    the structure required by the validator's `Resolve` branch. -/
def threeEntryValue (lovelace : Int) (ownHash : ByteString)
    (valQty : Int) (policyId assetName : ByteString)
    (assetAmount : Int) : Value :=
  [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)]),
   (Data.B ownHash, Data.Map [(Data.B "val", Data.I valQty)]),
   (Data.B policyId, Data.Map [(Data.B assetName, Data.I assetAmount)])]

/-! Defined as the stdlib's `validTxOutValue` ledger predicate applied
    to the continuation. For our literal `threeEntryValue`, this
    reduces to the strict-ordering and positivity invariants that the
    ledger guarantees on-chain. -/
def wellFormedResolveValue
    (lovelace : Int) (ownHash : ByteString) (valQty : Int)
    (policyId assetName : ByteString) (assetAmount : Int) : Prop :=
  CardanoLedgerApi.V1.Contexts.validTxOutValue
    (threeEntryValue lovelace ownHash valQty policyId assetName assetAmount) = true

/-- Spec for a valid `Resolve` transaction. The continuation must:
    * live at the script's own address,
    * preserve or increase lovelace,
    * carry exactly one `val` token under the script's own policy,
    * hold at least `amount` of the requested asset, and
    * carry a datum equal to the input's, except the `tag` is set to
      `some own_ref` (binding the continuation to the input). -/
def validResolve
    (ownHash : ByteString) (inDatum contDatum : Datum)
    (ownRef : TxOutRef) (contAddr : Address)
    (inLovelace contLovelace contValQty contAssetAmount : Int) : Prop :=
  contAddr = scriptAddr ownHash ∧
  inLovelace ≤ contLovelace ∧
  contValQty = 1 ∧
  contAssetAmount ≥ inDatum.amount ∧
  contDatum = { inDatum with tag := some ownRef }

/-- Spec for a valid `Close` spend. Four invariants are enforced:
    * the signer matches the datum's owner,
    * the mint policy of the burn is the script's own hash,
    * the burnt asset name is the literal `"val"`,
    * the burnt quantity is strictly negative. -/
def validClose
    (ownHash owner signer : ByteString)
    (mintPolicy mintAssetName : ByteString)
    (burnedQty : Int) : Prop :=
  signer = owner ∧
  mintPolicy = ownHash ∧
  mintAssetName = "val" ∧
  burnedQty < 0

/-- Spec for a valid `Mint`. The minting policy enforces four conditions
    on the order output and on the minted quantity:
    * the order output sits at an address whose payment credential is
      `Script policyId`,
    * the order output's value carries exactly 1 unit of `(policyId, "val")`,
    * the total minted quantity of `(policyId, "val")` is exactly 1,
    * the initial datum's `tag` is `none` (the `Resolve` branch later
      replaces it with the spent `own_ref`, enforcing uniqueness). -/
def validMint
    (policyId : ByteString) (orderAddr : Address)
    (orderValQty mintedQty : Int) (tag : Option TxOutRef) : Prop :=
  orderAddr.addressCredential = Credential.ScriptCredential policyId ∧
  orderValQty = 1 ∧
  mintedQty = 1 ∧
  tag = none

/-- Spec for a valid `Burn`: the minted quantity is strictly negative. -/
def validBurn (burnedQty : Int) : Prop := burnedQty < 0

end Properties.Order.Spec
