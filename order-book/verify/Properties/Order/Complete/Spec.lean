import CardanoLedgerApi.V3
import CardanoLedgerApi.V1.Contexts
import Properties.Order.Common

/-! Pure Lean specification, datum encoding and transaction shapes for
    the complete `order` validator. The `Vulnerable` variant reuses the
    same datum/transaction shapes from this module; only its
    `validResolve` predicate (in `Vulnerable/Spec.lean`) differs.

    Anti-double-satisfaction strategy: the `Resolve` branch updates the
    continuation datum's `tag` field to the current `own_ref`, binding
    the produced continuation to the input being spent. -/

namespace Properties.Order.Complete.Spec

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Address Credential OutputDatum ScriptContext ScriptPurpose
                          TxInInfo TxOut TxOutRef Value)
open Properties.Order.Common (InputValue RedeemerKind redeemerKindData
                              inputValueToValue scriptAddr)

/-- Datum carried by every UTxO at the `order` validator. The `tag`
    field is the anti-double-satisfaction binding (set to the spent
    `own_ref` by `Resolve`, `none` at mint time). -/
structure OrderDatum where
  owner : ByteString
  amount : Int
  policyId : ByteString
  assetName : ByteString
  tag : Option TxOutRef

def tagData : Option TxOutRef → Data
  | none => Data.Constr 1 []
  | some ref => Data.Constr 0 [IsData.toData ref]

def orderDatumData (d : OrderDatum) : Data :=
  Data.Constr 0
    [Data.B d.owner, Data.I d.amount, Data.B d.policyId,
     Data.B d.assetName, tagData d.tag]

/-- Well-formedness of a `Resolve` continuation value: the ledger's
    `validTxOutValue` predicate applied to the canonical three-entry
    layout (ada, `val` under `ownHash`, requested asset). -/
def wellFormedResolveValue
    (lovelace : Int) (ownHash : ByteString) (valQty : Int)
    (policyId assetName : ByteString) (assetAmount : Int) : Prop :=
  CardanoLedgerApi.V1.Contexts.validTxOutValue
    (inputValueToValue
      ⟨lovelace, ownHash, "val", valQty, policyId, assetName, assetAmount⟩) = true

/-- Script UTxO consumed by `Resolve`. -/
structure ResolveInput where
  ref   : TxOutRef
  datum : OrderDatum
  value : InputValue

/-- Continuation output produced by `Resolve`. `valQty` is the quantity
    of `val` under the script's own policy; `assetAmount` is the
    requested asset's quantity. -/
structure ResolveContinuation where
  address     : Address
  datum       : OrderDatum
  lovelace    : Int
  valQty      : Int
  assetAmount : Int

/-- `ScriptContext` for a `Resolve`-style transaction, parametric in
    the spend redeemer `r`. Completeness theorems instantiate
    `r := .Resolve 0`; soundness theorems quantify over `r`. -/
def resolveCtx
    (ownHash : ByteString)
    (input : ResolveInput) (cont : ResolveContinuation)
    (r : RedeemerKind)
    (fee : Int) (validRange : Data) (txId : ByteString)
    (treasuryAmount treasuryDonation : Data) : ScriptContext :=
  let ownAddr := scriptAddr ownHash
  let inResolved : TxOut :=
    ⟨ownAddr,
     inputValueToValue { input.value with policy1 := ownHash, asset1 := "val" },
     .OutputDatum (orderDatumData input.datum), none⟩
  let contValue :=
    inputValueToValue
      ⟨cont.lovelace, ownHash, "val", cont.valQty,
       input.datum.policyId, input.datum.assetName, cont.assetAmount⟩
  let contOutput : TxOut :=
    ⟨cont.address, contValue, .OutputDatum (orderDatumData cont.datum), none⟩
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨input.ref, inResolved⟩]
        txInfoReferenceInputs := []
        txInfoOutputs := [contOutput]
        txInfoFee := fee
        txInfoMint := []
        txInfoTxCerts := []
        txInfoWdrl := []
        txInfoValidRange := validRange
        txInfoSignatories := []
        txInfoRedeemers :=
          [(ScriptPurpose.Spending input.ref, redeemerKindData r)]
        txInfoData := []
        txInfoId := txId
        txInfoVotes := []
        txInfoProposalProcedures := []
        txInfoCurrentTreasuryAmount := treasuryAmount
        txInfoTreasuryDonation := treasuryDonation
      }
    scriptContextRedeemer := redeemerKindData r
    scriptContextScriptInfo :=
      .SpendingScript input.ref (some (orderDatumData input.datum))
  }

/-! ## Close transaction shape -/

/-- Script UTxO consumed by `Close`. -/
structure CloseInput where
  ref   : TxOutRef
  datum : OrderDatum
  value : InputValue

/-- Mint entry burning the `val` token. -/
structure CloseMint where
  policy    : ByteString
  assetName : ByteString
  burnedQty : Int

/-! ## Mint transaction shape -/

/-- Mint entry under the order policy. -/
structure MintAction where
  policyId  : ByteString
  mintedQty : Int

/-- Freshly created order UTxO. `valQty` is the quantity of `val`
    carried; `tag` is the initial datum's tag field. -/
structure MintOutput where
  address : Address
  valQty  : Int
  tag     : Option TxOutRef

/-! ## Double-satisfaction transaction shape -/

/-- Two script UTxOs at the same address sharing a datum. -/
structure DSInputs where
  datum  : OrderDatum
  ref1   : TxOutRef
  ref2   : TxOutRef
  value1 : InputValue
  value2 : InputValue

/-- Single continuation output shared by both inputs. -/
structure DSContinuation where
  datum       : OrderDatum
  lovelace    : Int
  valQty      : Int
  assetAmount : Int

/-- `ScriptContext` modelling a candidate double-satisfaction
    transaction. `ownRef` selects which input is the current validator
    invocation. -/
def doubleInputCtx
    (ownHash : ByteString)
    (inputs : DSInputs) (cont : DSContinuation)
    (ownRef : TxOutRef) (redeemer : RedeemerKind)
    (fee : Int) (validRange : Data) (txId : ByteString)
    (treasuryAmount treasuryDonation : Data) : ScriptContext :=
  let ownAddr := scriptAddr ownHash
  let inDatumD := orderDatumData inputs.datum
  let in1 : TxOut :=
    ⟨ownAddr,
     inputValueToValue { inputs.value1 with policy1 := ownHash, asset1 := "val" },
     .OutputDatum inDatumD, none⟩
  let in2 : TxOut :=
    ⟨ownAddr,
     inputValueToValue { inputs.value2 with policy1 := ownHash, asset1 := "val" },
     .OutputDatum inDatumD, none⟩
  let contValue :=
    inputValueToValue
      ⟨cont.lovelace, ownHash, "val", cont.valQty,
       inputs.datum.policyId, inputs.datum.assetName, cont.assetAmount⟩
  let contOutput : TxOut :=
    ⟨ownAddr, contValue, .OutputDatum (orderDatumData cont.datum), none⟩
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨inputs.ref1, in1⟩, ⟨inputs.ref2, in2⟩]
        txInfoReferenceInputs := []
        txInfoOutputs := [contOutput]
        txInfoFee := fee
        txInfoMint := []
        txInfoTxCerts := []
        txInfoWdrl := []
        txInfoValidRange := validRange
        txInfoSignatories := []
        txInfoRedeemers :=
          [(ScriptPurpose.Spending inputs.ref1, redeemerKindData redeemer),
           (ScriptPurpose.Spending inputs.ref2, redeemerKindData redeemer)]
        txInfoData := []
        txInfoId := txId
        txInfoVotes := []
        txInfoProposalProcedures := []
        txInfoCurrentTreasuryAmount := treasuryAmount
        txInfoTreasuryDonation := treasuryDonation
      }
    scriptContextRedeemer := redeemerKindData redeemer
    scriptContextScriptInfo :=
      .SpendingScript ownRef (some (orderDatumData inputs.datum))
  }

/-- Validator-level double-satisfaction prevention, parameterised by
    the validator's acceptance predicate. Holds when no transaction
    with two distinct script inputs and a single shared continuation
    can have both invocations accept, for any redeemer. -/
def noDoubleSatisfaction (acceptsProp : ScriptContext → Prop) : Prop :=
  ∀ (ownHash : ByteString) (inDatum contDatum : OrderDatum)
    (ref1 ref2 : TxOutRef)
    (value1 value2 : InputValue)
    (contLovelace contValQty contAssetAmount : Int)
    (redeemer : RedeemerKind)
    (fee : Int) (validRange : Data) (txId : ByteString)
    (treasuryAmount treasuryDonation : Data),
    ref1 ≠ ref2 →
    let inputs : DSInputs := ⟨inDatum, ref1, ref2, value1, value2⟩
    let cont : DSContinuation := ⟨contDatum, contLovelace, contValQty, contAssetAmount⟩
    ¬ (acceptsProp
          (doubleInputCtx ownHash inputs cont ref1 redeemer
                          fee validRange txId treasuryAmount treasuryDonation)
     ∧ acceptsProp
          (doubleInputCtx ownHash inputs cont ref2 redeemer
                          fee validRange txId treasuryAmount treasuryDonation))

/-- Resolve spec: the continuation lives at the script's own address,
    preserves or increases the input's lovelace, carries exactly one
    `val` token, holds at least `amount` of the requested asset, and
    propagates the input datum with `tag := some input.ref`. -/
def validResolve (ownHash : ByteString)
    (input : ResolveInput) (cont : ResolveContinuation) : Prop :=
  cont.address = scriptAddr ownHash ∧
  input.value.lovelace ≤ cont.lovelace ∧
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
