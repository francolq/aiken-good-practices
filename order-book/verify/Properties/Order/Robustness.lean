import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Order.Spec
import Properties.Order.Validator
import Properties.Order.MintValidator

/-! Robustness theorems for the compiled `order` validator . -/

namespace Properties.Order.Robustness

open CardanoLedgerApi.IsData.Class (IsData)
open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.V3 (Address Credential OutputDatum ScriptContext TxOut
                          TxOutRef lovelaceValue)
open Properties.Order.Spec
open Properties.Order.Validator (closeCtx dummyValidRange orderAcceptsProp
                                 orderDatumData orderTxId resolveCtx
                                 resolveRedeemer)
open Properties.Order.MintValidator (mintCtxMint orderMintAcceptsProp)

set_option warn.sorry false

/-- A continuation at the wrong address is rejected. -/
theorem resolve_rejects_wrong_address :
    ∀ (ownHash : ByteString) (inDatum contDatum : Datum)
      (ownRef : TxOutRef) (contAddr : Address)
      (inLovelace contLovelace : Int)
      (contValQty contAssetAmount : Int),
      contAddr ≠ scriptAddr ownHash →
      ¬ orderAcceptsProp
        (resolveCtx ownHash inDatum contDatum ownRef contAddr
                    inLovelace contLovelace contValQty contAssetAmount)
    := by blaster

/-- A continuation that loses lovelace is rejected. -/
theorem resolve_rejects_value_loss :
    ∀ (ownHash : ByteString) (inDatum contDatum : Datum)
      (ownRef : TxOutRef) (contAddr : Address)
      (inLovelace contLovelace : Int)
      (contValQty contAssetAmount : Int),
      contLovelace < inLovelace →
      ¬ orderAcceptsProp
        (resolveCtx ownHash inDatum contDatum ownRef contAddr
                    inLovelace contLovelace contValQty contAssetAmount)
    := by blaster

/-- A continuation whose datum does not equal `{ inDatum with tag := some ownRef }`
    is rejected. The validator's `Resolve` check requires the
    continuation to copy the input datum and set `tag` to the current
    `own_ref` (anti-double-satisfaction). -/
theorem resolve_rejects_datum_change :
    ∀ (ownHash : ByteString) (inDatum contDatum : Datum)
      (ownRef : TxOutRef) (contAddr : Address)
      (inLovelace contLovelace : Int)
      (contValQty contAssetAmount : Int),
      contDatum ≠ { inDatum with tag := some ownRef } →
      ¬ orderAcceptsProp
        (resolveCtx ownHash inDatum contDatum ownRef contAddr
                    inLovelace contLovelace contValQty contAssetAmount)
    := by blaster

/-- `ScriptContext` for a transaction with two script inputs (refs
    `ref1` and `ref2`, both at `ownAddr`) and a single shared
    continuation output (tagged with `taggedWith`). The `ownRef`
    parameter selects which of the two inputs is the current
    validator invocation's spent input. This models a candidate
    double-satisfaction transaction. -/
def doubleInputCtx
    (ownHash : ByteString) (inDatum contDatum : Datum)
    (ref1 ref2 ownRef : TxOutRef)
    (in1Lovelace in2Lovelace contLovelace : Int)
    (contValQty contAssetAmount : Int) : ScriptContext :=
  let ownAddr := scriptAddr ownHash
  let in1 : TxOut :=
    ⟨ownAddr, lovelaceValue in1Lovelace, .NoOutputDatum, none⟩
  let in2 : TxOut :=
    ⟨ownAddr, lovelaceValue in2Lovelace, .NoOutputDatum, none⟩
  let contValue :=
    threeEntryValue contLovelace ownHash contValQty
                    inDatum.policyId inDatum.assetName contAssetAmount
  let contOutput : TxOut :=
    ⟨ownAddr, contValue, .OutputDatum (orderDatumData contDatum), none⟩
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨ref1, in1⟩, ⟨ref2, in2⟩]
        txInfoReferenceInputs := []
        txInfoOutputs := [contOutput]
        txInfoFee := 0
        txInfoMint := []
        txInfoTxCerts := []
        txInfoWdrl := []
        txInfoValidRange := dummyValidRange
        txInfoSignatories := []
        txInfoRedeemers := []
        txInfoData := []
        txInfoId := orderTxId
        txInfoVotes := []
        txInfoProposalProcedures := []
        txInfoCurrentTreasuryAmount := IsData.toData (none : Option Int)
        txInfoTreasuryDonation := IsData.toData (none : Option Int)
      }
    scriptContextRedeemer := resolveRedeemer 0
    scriptContextScriptInfo :=
      .SpendingScript ownRef (some (orderDatumData inDatum))
  }

/-- Double-satisfaction prevention. A transaction with two script
    inputs (refs `ref1 ≠ ref2`) that tries to satisfy both spends
    against a single shared continuation cannot have both validator
    invocations accept. The continuation's `tag` field can equal at
    most one of `Some ref1`, `Some ref2`, so the invocation whose
    `ownRef` does not match the tag rejects, and the transaction as a
    whole fails. -/
theorem no_double_satisfaction :
    ∀ (ownHash : ByteString) (inDatum contDatum : Datum)
      (ref1 ref2 : TxOutRef)
      (in1Lovelace in2Lovelace contLovelace : Int)
      (contValQty contAssetAmount : Int),
      ref1 ≠ ref2 →
      ¬ (orderAcceptsProp
            (doubleInputCtx ownHash inDatum contDatum ref1 ref2 ref1
                            in1Lovelace in2Lovelace contLovelace
                            contValQty contAssetAmount)
         ∧ orderAcceptsProp
            (doubleInputCtx ownHash inDatum contDatum ref1 ref2 ref2
                            in1Lovelace in2Lovelace contLovelace
                            contValQty contAssetAmount))
    := by blaster

/-! ## Close-branch robustness

    The four invariants enforced by the `Close` branch of `order.ak`:
    signer = owner, mint policy = ownHash, mint asset name = `"val"`,
    burned quantity < 0. Each theorem isolates one. -/

/-- The transaction signer must equal the datum's owner. -/
theorem close_rejects_wrong_signer :
    ∀ (ownHash owner : ByteString) (ownRef : TxOutRef) (signer : ByteString)
      (mintPolicy mintAssetName : ByteString) (burnedQty : Int),
      signer ≠ owner →
      ¬ orderAcceptsProp
          (closeCtx ownHash owner ownRef signer
                    mintPolicy mintAssetName burnedQty)
    := by blaster

/-- The burn must happen under the script's own policy. -/
theorem close_rejects_wrong_mint_policy :
    ∀ (ownHash owner : ByteString) (ownRef : TxOutRef) (signer : ByteString)
      (mintPolicy mintAssetName : ByteString) (burnedQty : Int),
      mintPolicy ≠ ownHash →
      ¬ orderAcceptsProp
          (closeCtx ownHash owner ownRef signer
                    mintPolicy mintAssetName burnedQty)
    := by blaster

/-- The burnt asset must be literally `"val"`. -/
theorem close_rejects_wrong_mint_asset :
    ∀ (ownHash owner : ByteString) (ownRef : TxOutRef) (signer : ByteString)
      (mintPolicy mintAssetName : ByteString) (burnedQty : Int),
      mintAssetName ≠ "val" →
      ¬ orderAcceptsProp
          (closeCtx ownHash owner ownRef signer
                    mintPolicy mintAssetName burnedQty)
    := by blaster

/-- A non-negative quantity (zero or mint, instead of a strict burn)
    is rejected. -/
theorem close_rejects_nonneg_qty :
    ∀ (ownHash owner : ByteString) (ownRef : TxOutRef) (signer : ByteString)
      (mintPolicy mintAssetName : ByteString) (burnedQty : Int),
      burnedQty ≥ 0 →
      ¬ orderAcceptsProp
          (closeCtx ownHash owner ownRef signer
                    mintPolicy mintAssetName burnedQty)
    := by blaster

/-! ## Mint-branch robustness

    Each theorem isolates one of the four invariants enforced by the
    `Mint` branch of `order.ak` and shows that violating it forces
    rejection. The symbolic surface mirrors `mintCtxMint`: `policyId`,
    `orderAddr`, `orderValQty`, `mintedQty`, `tag`. -/

/-- The order output must sit at an address whose payment credential
    is `Script policyId`. -/
theorem mint_rejects_wrong_address :
    ∀ (policyId : ByteString) (orderAddr : Address)
      (orderValQty mintedQty : Int) (tag : Option TxOutRef),
      orderAddr.addressCredential ≠ Credential.ScriptCredential policyId →
      ¬ orderMintAcceptsProp
          (mintCtxMint policyId orderAddr orderValQty mintedQty tag)
    := by blaster

/-- The order output must carry exactly one `(policyId, "val")` unit. -/
theorem mint_rejects_wrong_val_qty :
    ∀ (policyId : ByteString) (orderAddr : Address)
      (orderValQty mintedQty : Int) (tag : Option TxOutRef),
      orderValQty ≠ 1 →
      ¬ orderMintAcceptsProp
          (mintCtxMint policyId orderAddr orderValQty mintedQty tag)
    := by blaster

/-- The total minted quantity of `(policyId, "val")` must be exactly 1. -/
theorem mint_rejects_wrong_mint_qty :
    ∀ (policyId : ByteString) (orderAddr : Address)
      (orderValQty mintedQty : Int) (tag : Option TxOutRef),
      mintedQty ≠ 1 →
      ¬ orderMintAcceptsProp
          (mintCtxMint policyId orderAddr orderValQty mintedQty tag)
    := by blaster

end Properties.Order.Robustness
