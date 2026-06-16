import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Order.Common
import Properties.Order.Complete.Spec

/-! Completeness theorems and execution wrappers for the compiled
    complete `order` minting policy. -/

namespace Properties.Order.Complete.MintCompleteness

open CardanoLedgerApi.IsData.Class (IsData toTerm)
open CardanoLedgerApi.V3 (Address OutputDatum ScriptContext ScriptPurpose TxOut TxOutRef
                          singleton)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Const Program)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)
open Properties.Order.Complete.Spec

set_option warn.sorry false

#import_uplc orderMintScript PlutusV3 flat_hex "Scripts/order_mint.flat"

def orderMintValidator : Program := orderMintScript.script

def orderMintAcceptsProp (ctx : ScriptContext) : Prop :=
  cekExecuteProgram orderMintValidator [toTerm ctx] 5000000
    = .Halt (.VCon Const.Unit)

def mintRedeemerMint : Data := Data.Constr 0 []
def mintRedeemerBurn : Data := Data.Constr 1 []

/-- `ScriptContext` for a `Mint` transaction. -/
def mintCtxMint
    (mint : MintAction) (output : MintOutput)
    (fee : Int) (validRange : Data) (txId : ByteString)
    (treasuryAmount treasuryDonation : Data) : ScriptContext :=
  let initialDatum : OrderDatum := ⟨"", 0, "", "", output.tag⟩
  let initialOutput : TxOut :=
    ⟨output.address, singleton mint.policyId "val" output.valQty,
     .OutputDatum (orderDatumData initialDatum), none⟩
  { scriptContextTxInfo :=
      { txInfoInputs := []
        txInfoReferenceInputs := []
        txInfoOutputs := [initialOutput]
        txInfoFee := fee
        txInfoMint := singleton mint.policyId "val" mint.mintedQty
        txInfoTxCerts := []
        txInfoWdrl := []
        txInfoValidRange := validRange
        txInfoSignatories := []
        txInfoRedeemers := [(ScriptPurpose.Minting mint.policyId, mintRedeemerMint)]
        txInfoData := []
        txInfoId := txId
        txInfoVotes := []
        txInfoProposalProcedures := []
        txInfoCurrentTreasuryAmount := treasuryAmount
        txInfoTreasuryDonation := treasuryDonation
      }
    scriptContextRedeemer := mintRedeemerMint
    scriptContextScriptInfo := .MintingScript mint.policyId
  }

/-- `ScriptContext` for a `Burn` transaction. -/
def burnCtx
    (policyId : ByteString) (burnedQty : Int)
    (fee : Int) (validRange : Data) (txId : ByteString)
    (treasuryAmount treasuryDonation : Data) : ScriptContext :=
  { scriptContextTxInfo :=
      { txInfoInputs := []
        txInfoReferenceInputs := []
        txInfoOutputs := []
        txInfoFee := fee
        txInfoMint := singleton policyId "val" burnedQty
        txInfoTxCerts := []
        txInfoWdrl := []
        txInfoValidRange := validRange
        txInfoSignatories := []
        txInfoRedeemers := [(ScriptPurpose.Minting policyId, mintRedeemerBurn)]
        txInfoData := []
        txInfoId := txId
        txInfoVotes := []
        txInfoProposalProcedures := []
        txInfoCurrentTreasuryAmount := treasuryAmount
        txInfoTreasuryDonation := treasuryDonation
      }
    scriptContextRedeemer := mintRedeemerBurn
    scriptContextScriptInfo := .MintingScript policyId
  }

/-- Completeness of the `Mint` branch. -/
theorem mint_complete :
    ∀ (mint : MintAction) (output : MintOutput)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      validMint mint output →
      orderMintAcceptsProp
        (mintCtxMint mint output
                     fee validRange txId treasuryAmount treasuryDonation)
    := by blaster

/-- Completeness of the `Burn` branch. -/
theorem burn_complete :
    ∀ (policyId : ByteString) (burnedQty : Int)
      (fee : Int) (validRange : Data) (txId : ByteString)
      (treasuryAmount treasuryDonation : Data),
      validBurn burnedQty →
      orderMintAcceptsProp
        (burnCtx policyId burnedQty
                 fee validRange txId treasuryAmount treasuryDonation)
    := by blaster

end Properties.Order.Complete.MintCompleteness
