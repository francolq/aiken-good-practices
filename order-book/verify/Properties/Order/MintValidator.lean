import PlutusCore.UPLC
import CardanoLedgerApi.V3
import CardanoLedgerApi.V1.Time
import Blaster
import Properties.Order.Spec
import Properties.Order.Validator

/-! Completeness theorems and execution wrappers for the compiled
    `order` minting policy. Kept in its own module so the Blaster
    invocations do not compound with the spend ones. -/

namespace Properties.Order.MintValidator

open CardanoLedgerApi.IsData.Class (IsData toTerm)
open CardanoLedgerApi.V3 (Address OutputDatum ScriptContext TxOut TxOutRef
                          singleton)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Const Program)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)
open Properties.Order.Spec
open Properties.Order.Validator (dummyValidRange orderDatumData orderTxId)

set_option warn.sorry false

#import_uplc orderMintScript PlutusV3 flat_hex "Scripts/order_mint.flat"

def orderMintValidator : Program := orderMintScript.script

def orderMintAcceptsProp (ctx : ScriptContext) : Prop :=
  cekExecuteProgram orderMintValidator [toTerm ctx] 5000000
    = .Halt (.VCon Const.Unit)

def mintRedeemerMint : Data := Data.Constr 0 []
def mintRedeemerBurn : Data := Data.Constr 1 []

/-- `ScriptContext` for a `Mint` transaction. Symbolic parameters:
    `policyId`, the order output's `orderAddr`, the order output's
    quantity of `val` (`orderValQty`), the total minted quantity
    (`mintedQty`) and the initial datum's `tag`. The other datum
    fields stay concrete since the `Mint` branch ignores them. -/
def mintCtxMint
    (policyId : ByteString) (orderAddr : Address)
    (orderValQty mintedQty : Int) (tag : Option TxOutRef)
    : ScriptContext :=
  let initialDatum : Datum := ⟨"", 0, "", "", tag⟩
  let initialOutput : TxOut :=
    ⟨orderAddr, singleton policyId "val" orderValQty,
     .OutputDatum (orderDatumData initialDatum), none⟩
  { scriptContextTxInfo :=
      { txInfoInputs := []
        txInfoReferenceInputs := []
        txInfoOutputs := [initialOutput]
        txInfoFee := 0
        txInfoMint := singleton policyId "val" mintedQty
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
    scriptContextRedeemer := mintRedeemerMint
    scriptContextScriptInfo := .MintingScript policyId
  }

/-- `ScriptContext` for a `Burn` transaction. -/
def burnCtx (policyId : ByteString) (burnedQty : Int) : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs := []
        txInfoReferenceInputs := []
        txInfoOutputs := []
        txInfoFee := 0
        txInfoMint := singleton policyId "val" burnedQty
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
    scriptContextRedeemer := mintRedeemerBurn
    scriptContextScriptInfo := .MintingScript policyId
  }

/-- Completeness of the `Mint` branch. -/
theorem mint_complete :
    ∀ (policyId : ByteString) (orderAddr : Address)
      (orderValQty mintedQty : Int) (tag : Option TxOutRef),
      validMint policyId orderAddr orderValQty mintedQty tag →
      orderMintAcceptsProp
        (mintCtxMint policyId orderAddr orderValQty mintedQty tag)
    := by blaster

/-- Completeness of the `Burn` branch. -/
theorem burn_complete :
    ∀ (policyId : ByteString) (burnedQty : Int),
      validBurn burnedQty →
      orderMintAcceptsProp (burnCtx policyId burnedQty)
    := by blaster

end Properties.Order.MintValidator
