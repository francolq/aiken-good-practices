import PlutusCore.UPLC
import CardanoLedgerApi.V3
import CardanoLedgerApi.V1.Contexts
import Properties.Common

/-! # Specification

    Each property is a single `def <name>_theorem (validator : Program) ... : Prop`
    with the `ScriptContext` built inline; the theorem *is* the spec, and every
    validator is compared against it. Parameters are `validator` plus the values
    that vary per validator: the datum, its encoding, the continuation datum, and
    the redeemer. -/

namespace Properties.Spec

open PlutusCore.UPLC.Term (Program)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Address Credential Redeemer ScriptContext TxInfo TxOut TxOutRef
                          Value OutputDatum ScriptPurpose valueOf singleton)
open Properties.Common (validatorAccepts)

/-- The (fake) hash of the script under test, its address, and the
    output reference of the order UTxO being spent. -/
def scriptHash : ByteString := "fake_script_hash_28bytes!!!!"
def scriptAddr : Address := ⟨.ScriptCredential scriptHash, none⟩
def orderRef : TxOutRef := ⟨"txid_placeholder_32bytes!!!!!!!!", 0⟩

/-- The common datum fields the spec reasons about. The on-chain
    encoding is passed separately (it differs per validator). -/
structure OrderDatum where
  owner     : ByteString
  amount    : Int
  policyId  : ByteString
  assetName : ByteString

/-- 4-field on-chain datum encoding (minimal validators). -/
def encode4 (d : OrderDatum) : Data :=
  Data.Constr 0 [Data.B d.owner, Data.I d.amount, Data.B d.policyId, Data.B d.assetName]

def tagData : Option TxOutRef → Data
  | none     => Data.Constr 1 []
  | some ref => Data.Constr 0 [IsData.toData ref]

/-- 5-field on-chain datum encoding with the anti-double-satisfaction
    `tag` (complete / vulnerable validators). -/
def encode5 (d : OrderDatum) (tag : Option TxOutRef) : Data :=
  Data.Constr 0 [Data.B d.owner, Data.I d.amount, Data.B d.policyId,
                 Data.B d.assetName, tagData tag]

/-- Shared transaction skeleton. -/
def baseTxInfo : TxInfo :=
  { txInfoInputs := []
    txInfoReferenceInputs := []
    txInfoOutputs := []
    txInfoFee := 0
    txInfoMint := []
    txInfoTxCerts := []
    txInfoWdrl := []
    txInfoValidRange := IsData.toData (none : Option Int)
    txInfoSignatories := []
    txInfoRedeemers := []
    txInfoData := []
    txInfoId := "txid_placeholder_32bytes!!!!!!!!"
    txInfoVotes := []
    txInfoProposalProcedures := []
    txInfoCurrentTreasuryAmount := IsData.toData (none : Option Int)
    txInfoTreasuryDonation := IsData.toData (none : Option Int)
  }

/-- Set the fee, validity range, tx id and treasury fields on a skeleton. -/
def withEnv (fee : Int) (validRange : Data) (txId : ByteString)
    (treasuryAmount treasuryDonation : Data) (txInfo : TxInfo) : TxInfo :=
  { txInfo with
    txInfoFee := fee
    txInfoValidRange := validRange
    txInfoId := txId
    txInfoCurrentTreasuryAmount := treasuryAmount
    txInfoTreasuryDonation := treasuryDonation }

/-- An order UTxO value: ada plus the validity token under the script's
    own policy. -/
def orderValue (lovelace valQty : Int) : Value :=
  [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)]),
   (Data.B scriptHash, Data.Map [(Data.B "val", Data.I valQty)])]

/-- A continuation value: ada, the asked asset, and the validity token
    (entries ordered canonically by policy id). -/
def resolvedValue (lovelace valQty askedQty : Int)
    (askedPolicy askedName : ByteString) : Value :=
  [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)]),
   (Data.B askedPolicy, Data.Map [(Data.B askedName, Data.I askedQty)]),
   (Data.B scriptHash, Data.Map [(Data.B "val", Data.I valQty)])]

/-- Well-formedness of a `Resolve` continuation value: `validTxOutValue` on the
    canonical layout. Excludes the degenerate cases where the asked asset aliases
    ada (`""`) or the validity token (`scriptHash`/`"val"`). -/
def wellFormedResolveValue (lovelace valQty askedQty : Int)
    (askedPolicy askedName : ByteString) : Prop :=
  CardanoLedgerApi.V1.Contexts.validTxOutValue
    (resolvedValue lovelace valQty askedQty askedPolicy askedName) = true

/-- A UTxO sits at the script address and carries the given datum. -/
def validOrder (utxo : TxOut) (datumData : Data) : Prop :=
  utxo.txOutAddress = scriptAddr ∧
  utxo.txOutDatum = .OutputDatum datumData

/-- The continuation keeps the script address and pays at least `amount`
    more of the asked asset than the input held (Theorem 2, resolve). -/
def validTransition (utxo contUtxo : TxOut) (datum : OrderDatum) : Prop :=
  contUtxo.txOutAddress = utxo.txOutAddress ∧
  valueOf datum.policyId datum.assetName contUtxo.txOutValue ≥
    valueOf datum.policyId datum.assetName utxo.txOutValue + datum.amount

/-- Soundness: a valid order UTxO can be spent (resolve) only if the
    continuation stays at the script address and pays the asked asset.
    `datum`/`inDatumData`/`contDatumData`/`redeemer` are the
    per-validator parameters. -/
def spend_sound_theorem (validator : Program)
    (datum : OrderDatum) (inDatumData contDatumData : Data)
    (redeemer : Redeemer) : Prop :=
  ∀ (fee : Int) (validRange : Data) (txId : ByteString) (treasuryAmount treasuryDonation : Data) (outAddr : Address)
    (inLovelace inVal : Int)
    (outLovelace outVal outAsked : Int),
    let utxo : TxOut :=
      ⟨scriptAddr, orderValue inLovelace inVal, .OutputDatum inDatumData, none⟩
    let contUtxo : TxOut :=
      ⟨outAddr,
       resolvedValue outLovelace outVal outAsked datum.policyId datum.assetName,
       .OutputDatum contDatumData, none⟩
    let txInfo : TxInfo :=
      withEnv fee validRange txId treasuryAmount treasuryDonation { baseTxInfo with
        txInfoInputs := [⟨orderRef, utxo⟩]
        txInfoOutputs := [contUtxo]
        txInfoRedeemers := [(.Spending orderRef, redeemer)] }
    let ctx : ScriptContext :=
      { scriptContextTxInfo := txInfo
        scriptContextRedeemer := redeemer
        scriptContextScriptInfo := .SpendingScript orderRef (some inDatumData) }
    wellFormedResolveValue outLovelace outVal outAsked datum.policyId datum.assetName ∧
    inLovelace > 0 ∧ outLovelace > 0 ∧
    validOrder utxo inDatumData ∧
    validatorAccepts ctx validator →
    validTransition utxo contUtxo datum

/-- Completeness (Theorem 3): a valid order UTxO *can* be spent (resolve)
    by paying at least the asked asset and amount into a continuation at
    the script address. -/
def spend_complete_theorem (validator : Program)
    (datum : OrderDatum) (inDatumData contDatumData : Data)
    (redeemer : Redeemer) : Prop :=
  ∀ (fee : Int) (validRange : Data) (txId : ByteString) (treasuryAmount treasuryDonation : Data) (inLovelace inVal : Int)
    (outLovelace outVal outAsked : Int),
    let utxo : TxOut :=
      ⟨scriptAddr, orderValue inLovelace inVal, .OutputDatum inDatumData, none⟩
    let contUtxo : TxOut :=
      ⟨scriptAddr,
       resolvedValue outLovelace outVal outAsked datum.policyId datum.assetName,
       .OutputDatum contDatumData, none⟩
    let txInfo : TxInfo :=
      withEnv fee validRange txId treasuryAmount treasuryDonation { baseTxInfo with
        txInfoInputs := [⟨orderRef, utxo⟩]
        txInfoOutputs := [contUtxo]
        txInfoRedeemers := [(.Spending orderRef, redeemer)] }
    let ctx : ScriptContext :=
      { scriptContextTxInfo := txInfo
        scriptContextRedeemer := redeemer
        scriptContextScriptInfo := .SpendingScript orderRef (some inDatumData) }
    wellFormedResolveValue outLovelace outVal outAsked datum.policyId datum.assetName ∧
    inLovelace > 0 ∧ outLovelace ≥ inLovelace ∧
    outVal = 1 ∧ outAsked ≥ datum.amount →
    validatorAccepts ctx validator

/-- The `Close` redeemer (second constructor) and the `Burn` mint
    redeemer, shared by every validator. -/
def closeRedeemer : Redeemer := Data.Constr 1 []
def burnRedeemer : Redeemer := Data.Constr 1 []

/-- The `Close` transaction shape: the order input, the owner's
    signature, and a burn of the validity token (which the minimal
    validators ignore). -/
def closeCtx (fee : Int) (validRange : Data) (txId : ByteString) (treasuryAmount treasuryDonation : Data) (_datum : OrderDatum) (inDatumData : Data)
    (signer : ByteString) (inLovelace inVal burnedQty : Int) : ScriptContext :=
  let utxo : TxOut :=
    ⟨scriptAddr, orderValue inLovelace inVal, .OutputDatum inDatumData, none⟩
  let txInfo : TxInfo :=
    withEnv fee validRange txId treasuryAmount treasuryDonation { baseTxInfo with
      txInfoInputs := [⟨orderRef, utxo⟩]
      txInfoMint := singleton scriptHash "val" burnedQty
      txInfoSignatories := [signer]
      txInfoRedeemers :=
        [(ScriptPurpose.Spending orderRef, closeRedeemer),
         (ScriptPurpose.Minting scriptHash, burnRedeemer)] }
  { scriptContextTxInfo := txInfo
    scriptContextRedeemer := closeRedeemer
    scriptContextScriptInfo := .SpendingScript orderRef (some inDatumData) }

/-- Close soundness (Theorem 2, close): a valid order can be spent via
    `Close` only if the transaction is signed by the owner. -/
def close_sound_theorem (validator : Program)
    (datum : OrderDatum) (inDatumData : Data) : Prop :=
  ∀ (fee : Int) (validRange : Data) (txId : ByteString) (treasuryAmount treasuryDonation : Data) (signer : ByteString) (inLovelace inVal burnedQty : Int),
    let utxo : TxOut :=
      ⟨scriptAddr, orderValue inLovelace inVal, .OutputDatum inDatumData, none⟩
    inLovelace > 0 ∧
    validOrder utxo inDatumData ∧
    validatorAccepts (closeCtx fee validRange txId treasuryAmount treasuryDonation datum inDatumData signer inLovelace inVal burnedQty) validator →
    signer = datum.owner

/-- Close completeness (Theorem 1): a valid order UTxO can be spent by
    its owner (who signs and burns the validity token). -/
def close_complete_theorem (validator : Program)
    (datum : OrderDatum) (inDatumData : Data) : Prop :=
  ∀ (fee : Int) (validRange : Data) (txId : ByteString) (treasuryAmount treasuryDonation : Data) (inLovelace inVal burnedQty : Int),
    inLovelace > 0 ∧ burnedQty < 0 →
    validatorAccepts
      (closeCtx fee validRange txId treasuryAmount treasuryDonation datum inDatumData datum.owner inLovelace inVal burnedQty) validator

/-- No double satisfaction: a transaction with two distinct order inputs
    and a single shared continuation cannot have both spend-validations
    accept. `ctx1`/`ctx2` are the same transaction seen from each input
    (`scriptContextScriptInfo` selects which input is being validated). -/
def no_double_satisfaction_theorem (validator : Program)
    (datum : OrderDatum) (inDatumData contDatumData : Data)
    (redeemer : Redeemer) : Prop :=
  ∀ (fee : Int) (validRange : Data) (txId : ByteString) (treasuryAmount treasuryDonation : Data) (ref1 ref2 : TxOutRef)
    (in1Lovelace in1Val in2Lovelace in2Val : Int)
    (outLovelace outVal outAsked : Int)
    (contAddr : Address),
    ref1 ≠ ref2 →
    let in1 : TxOut :=
      ⟨scriptAddr, orderValue in1Lovelace in1Val, .OutputDatum inDatumData, none⟩
    let in2 : TxOut :=
      ⟨scriptAddr, orderValue in2Lovelace in2Val, .OutputDatum inDatumData, none⟩
    let contUtxo : TxOut :=
      ⟨contAddr,
       resolvedValue outLovelace outVal outAsked datum.policyId datum.assetName,
       .OutputDatum contDatumData, none⟩
    let txInfo : TxInfo :=
      withEnv fee validRange txId treasuryAmount treasuryDonation { baseTxInfo with
        txInfoInputs := [⟨ref1, in1⟩, ⟨ref2, in2⟩]
        txInfoOutputs := [contUtxo]
        txInfoRedeemers :=
          [(ScriptPurpose.Spending ref1, redeemer),
           (ScriptPurpose.Spending ref2, redeemer)] }
    let ctx1 : ScriptContext :=
      { scriptContextTxInfo := txInfo
        scriptContextRedeemer := redeemer
        scriptContextScriptInfo := .SpendingScript ref1 (some inDatumData) }
    let ctx2 : ScriptContext :=
      { scriptContextTxInfo := txInfo
        scriptContextRedeemer := redeemer
        scriptContextScriptInfo := .SpendingScript ref2 (some inDatumData) }
    ¬ (validatorAccepts ctx1 validator ∧ validatorAccepts ctx2 validator)

/-! ## Minting policy (complete / vulnerable validators) -/

def mintRedeemer : Redeemer := Data.Constr 0 []

/-- A `Mint` transaction: one order output carrying the minted `val`
    token. -/
def mintCtx (fee : Int) (validRange : Data) (txId : ByteString) (treasuryAmount treasuryDonation : Data) (orderAddr : Address) (orderValQty mintedQty : Int)
    (orderDatumData : Data) : ScriptContext :=
  let orderOut : TxOut :=
    ⟨orderAddr, singleton scriptHash "val" orderValQty,
     .OutputDatum orderDatumData, none⟩
  let txInfo : TxInfo :=
    withEnv fee validRange txId treasuryAmount treasuryDonation { baseTxInfo with
      txInfoOutputs := [orderOut]
      txInfoMint := singleton scriptHash "val" mintedQty
      txInfoRedeemers := [(ScriptPurpose.Minting scriptHash, mintRedeemer)] }
  { scriptContextTxInfo := txInfo
    scriptContextRedeemer := mintRedeemer
    scriptContextScriptInfo := .MintingScript scriptHash }

/-- A `Burn` transaction. -/
def burnCtx (fee : Int) (validRange : Data) (txId : ByteString) (treasuryAmount treasuryDonation : Data) (burnedQty : Int) : ScriptContext :=
  let txInfo : TxInfo :=
    withEnv fee validRange txId treasuryAmount treasuryDonation { baseTxInfo with
      txInfoMint := singleton scriptHash "val" burnedQty
      txInfoRedeemers := [(ScriptPurpose.Minting scriptHash, burnRedeemer)] }
  { scriptContextTxInfo := txInfo
    scriptContextRedeemer := burnRedeemer
    scriptContextScriptInfo := .MintingScript scriptHash }

/-- Mint spec: the order output sits at the policy's own script address
    and carries exactly one minted `val` token. -/
def validMint (orderAddr : Address) (orderValQty mintedQty : Int) : Prop :=
  orderAddr.addressCredential = Credential.ScriptCredential scriptHash ∧
  orderValQty = 1 ∧ mintedQty = 1

def mint_complete_theorem (mintValidator : Program) (orderDatumData : Data) : Prop :=
  ∀ (fee : Int) (validRange : Data) (txId : ByteString) (treasuryAmount treasuryDonation : Data) (orderAddr : Address) (orderValQty mintedQty : Int),
    validMint orderAddr orderValQty mintedQty →
    validatorAccepts (mintCtx fee validRange txId treasuryAmount treasuryDonation orderAddr orderValQty mintedQty orderDatumData) mintValidator

def mint_sound_theorem (mintValidator : Program) (orderDatumData : Data) : Prop :=
  ∀ (fee : Int) (validRange : Data) (txId : ByteString) (treasuryAmount treasuryDonation : Data) (orderAddr : Address) (orderValQty mintedQty : Int),
    validatorAccepts (mintCtx fee validRange txId treasuryAmount treasuryDonation orderAddr orderValQty mintedQty orderDatumData) mintValidator →
    validMint orderAddr orderValQty mintedQty

def burn_complete_theorem (mintValidator : Program) : Prop :=
  ∀ (fee : Int) (validRange : Data) (txId : ByteString) (treasuryAmount treasuryDonation : Data) (burnedQty : Int),
    burnedQty < 0 → validatorAccepts (burnCtx fee validRange txId treasuryAmount treasuryDonation burnedQty) mintValidator

def burn_sound_theorem (mintValidator : Program) : Prop :=
  ∀ (fee : Int) (validRange : Data) (txId : ByteString) (treasuryAmount treasuryDonation : Data) (burnedQty : Int),
    validatorAccepts (burnCtx fee validRange txId treasuryAmount treasuryDonation burnedQty) mintValidator → burnedQty < 0

end Properties.Spec
