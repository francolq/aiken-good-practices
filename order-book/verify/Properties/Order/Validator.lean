import PlutusCore.UPLC
import CardanoLedgerApi.V3
import CardanoLedgerApi.V1.Time
import Blaster
import Properties.Order.Spec

/-! Completeness theorems and execution wrappers for the compiled
    `order` spending validator .See `Properties.Order.Robustness`
    for rejection theorems and `Properties.Order.Soundness` for the
    soundness direction. -/

namespace Properties.Order.Validator

open CardanoLedgerApi.IsData.Class (IsData toTerm)
open CardanoLedgerApi.V3 (Address Credential CurrencySymbol OutputDatum
                          ScriptContext ScriptInfo TokenName
                          TxInInfo TxOut TxOutRef Value
                          lovelaceValue singleton)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Const Program)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)
open Properties.Order.Spec

set_option warn.sorry false

#import_uplc orderScript PlutusV3 flat_hex "Scripts/order_spend.flat"
-- Direct cek: with a universally quantified `ctx`, `#prep_uplc` cannot
-- reduce `toTerm ctx` symbolically (the term stays stuck on the
-- quantified context), so we build concrete contexts and run the
-- script through `cekExecuteProgram`.
def orderValidator : Program := orderScript.script

def orderAcceptsProp (ctx : ScriptContext) : Prop :=
  cekExecuteProgram orderValidator [toTerm ctx] 5000000
    = .Halt (.VCon Const.Unit)

/-! ## Data encodings of Datum and Redeemer

    The Aiken types are:
    ```
    pub type OrderDatum {
      owner: VerificationKeyHash,
      amount: Int,
      policy_id: PolicyId,
      asset_name: AssetName,
      tag: Option<OutputReference>,
    }
    pub type OrderRedeemer {
      Resolve(Int)
      Close
    }
    ```
-/

def tagData : Option TxOutRef → Data
  | none => Data.Constr 1 []
  | some ref => Data.Constr 0 [IsData.toData ref]

def orderDatumData (d : Datum) : Data :=
  Data.Constr 0
    [Data.B d.owner, Data.I d.amount, Data.B d.policyId,
     Data.B d.assetName, tagData d.tag]

def resolveRedeemer (outIx : Int) : Data := Data.Constr 0 [Data.I outIx]
def closeRedeemer : Data := Data.Constr 1 []

def dummyValidRange : Data := IsData.toData CardanoLedgerApi.V1.Time.everything
def orderTxId : ByteString := "27ae41e4649b934ca495991b7852b855"

/-- `ScriptContext` for a `Resolve 0` transaction.

    Inputs: a single script input at `ownRef` carrying `inDatum`, with
    address `scriptAddr ownHash` and `inLovelace` ada.

    Outputs: a single continuation at index 0 with address `contAddr`,
    value `(contLovelace ada, contValQty val under ownHash,
    contAssetAmount of (inDatum.policyId, inDatum.assetName))`, and
    datum `contDatum`. -/
def resolveCtx
    (ownHash : ByteString) (inDatum contDatum : Datum)
    (ownRef : TxOutRef) (contAddr : Address)
    (inLovelace contLovelace : Int)
    (contValQty contAssetAmount : Int) : ScriptContext :=
  let ownAddr := scriptAddr ownHash
  let inResolved : TxOut :=
    ⟨ownAddr, lovelaceValue inLovelace, .NoOutputDatum, none⟩
  let contValue :=
    threeEntryValue contLovelace ownHash contValQty
                    inDatum.policyId inDatum.assetName contAssetAmount
  let contOutput : TxOut :=
    ⟨contAddr, contValue, .OutputDatum (orderDatumData contDatum), none⟩
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨ownRef, inResolved⟩]
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

/-- `ScriptContext` for a `Close` transaction. Symbolic parameters:
    `ownHash`, the datum's `owner`, `ownRef`, the sole `signer`, the
    mint's policy id and asset name (`mintPolicy`, `mintAssetName`),
    and the burned quantity. The remaining datum fields are concrete
    (the `Close` branch ignores them). -/
def closeCtx
    (ownHash owner : ByteString) (ownRef : TxOutRef) (signer : ByteString)
    (mintPolicy mintAssetName : ByteString) (burnedQty : Int)
    : ScriptContext :=
  let ownAddr := scriptAddr ownHash
  let inDatum : Datum := ⟨owner, 0, "", "", none⟩
  let inResolved : TxOut :=
    ⟨ownAddr, lovelaceValue 0, .NoOutputDatum, none⟩
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨ownRef, inResolved⟩]
        txInfoReferenceInputs := []
        txInfoOutputs := []
        txInfoFee := 0
        txInfoMint := singleton mintPolicy mintAssetName burnedQty
        txInfoTxCerts := []
        txInfoWdrl := []
        txInfoValidRange := dummyValidRange
        txInfoSignatories := [signer]
        txInfoRedeemers := []
        txInfoData := []
        txInfoId := orderTxId
        txInfoVotes := []
        txInfoProposalProcedures := []
        txInfoCurrentTreasuryAmount := IsData.toData (none : Option Int)
        txInfoTreasuryDonation := IsData.toData (none : Option Int)
      }
    scriptContextRedeemer := closeRedeemer
    scriptContextScriptInfo :=
      .SpendingScript ownRef (some (orderDatumData inDatum))
  }

/-- Completeness of the `Resolve` branch. -/
theorem resolve_complete :
    ∀ (ownHash : ByteString) (inDatum contDatum : Datum)
      (ownRef : TxOutRef) (contAddr : Address)
      (inLovelace contLovelace : Int)
      (contValQty contAssetAmount : Int),
      wellFormedResolveValue contLovelace ownHash contValQty
                             inDatum.policyId inDatum.assetName contAssetAmount →
      validResolve ownHash inDatum contDatum ownRef contAddr
                   inLovelace contLovelace contValQty contAssetAmount →
      orderAcceptsProp
        (resolveCtx ownHash inDatum contDatum ownRef contAddr
                    inLovelace contLovelace contValQty contAssetAmount)
    := by blaster

/-- Completeness of the `Close` branch. -/
theorem close_complete :
    ∀ (ownHash owner : ByteString) (ownRef : TxOutRef) (signer : ByteString)
      (mintPolicy mintAssetName : ByteString) (burnedQty : Int),
      validClose ownHash owner signer mintPolicy mintAssetName burnedQty →
      orderAcceptsProp
        (closeCtx ownHash owner ownRef signer
                  mintPolicy mintAssetName burnedQty)
    := by blaster

end Properties.Order.Validator
