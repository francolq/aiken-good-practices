import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Properties.Common

namespace Properties.Soundness

open PlutusCore.UPLC.Term (Program)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Address Datum Redeemer ScriptContext StakingCredential
                          TxInfo TxInInfo TxOut Value OutputDatum PubKeyHash
                          validScriptContext lovelaceValue valueOf singleton add)

set_option warn.sorry false

structure OrderDatum where
  owner : ByteString
  amount : Int
  policyId : ByteString
  assetName : ByteString

def orderDatum (orderData : Data) : OrderDatum :=
  match orderData with
  | Data.Constr 0
      ( Data.B owner ::
        Data.I amount ::
        Data.B policyId ::
        Data.B assetName ::
        _
      ) =>
      { owner := owner
        amount := amount
        policyId := policyId
        assetName := assetName
      }
  | _ =>
      { owner := default
        amount := default
        policyId := default
        assetName := default
      }

def baseTxInfo: TxInfo :=
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
    txInfoId := "fake_txid_32bytes!!!!!!!!!!!!!!!"
    txInfoVotes := []
    txInfoProposalProcedures := []
    txInfoCurrentTreasuryAmount := IsData.toData (none : Option Int)
    txInfoTreasuryDonation := IsData.toData (none : Option Int)
  }

-- datum is not checked (it is assumed to be valid)
def validOrder (utxo : TxOut) : Prop :=
  -- TODO: staking could be any
  utxo.txOutAddress.addressCredential = .ScriptCredential "fake_script_hash_28bytes!!!!"

/--
  Checks correct execution of a resolve operation.
  For optimization, input datum is assumed to be already parsed in `inDatum`.
  Checks:
  - address preserved
  - datum is inline, first four fields are as in inDatum.
    Rest of datum can be anything.
  - in value, asked asset is added in required amount.
    Rest of value can be anything.
  - ref script not checked
--/
def validResolve (utxo contUtxo : TxOut) (inDatum : OrderDatum) : Prop :=
  contUtxo.txOutAddress = utxo.txOutAddress ∧
  if let .OutputDatum outDatum := utxo.txOutDatum then
    inDatum = orderDatum outDatum ∧
    let askedPolicy := inDatum.policyId
    let askedAssetName := inDatum.assetName
    valueOf askedPolicy askedAssetName contUtxo.txOutValue ≥
    valueOf askedPolicy askedAssetName utxo.txOutValue + inDatum.amount
  else
    false

def hasOutputs (ctx : ScriptContext) (outs : List TxOut) : Prop :=
  ctx.scriptContextTxInfo.txInfoOutputs = outs

def hasInputs (ctx : ScriptContext) (ins : List TxInInfo) : Prop :=
  ctx.scriptContextTxInfo.txInfoInputs = ins

def orderValue (lovelace a : Int) : Value :=
    if a = 0 then
      [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)])]
    else
      [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)]),
        (Data.B "fake_policyA_hash_28bytes!!!",
        Data.Map [(Data.B "fake_asset_nameA", Data.I a)])]

def orderValue2 (lovelace a b : Int) : Value :=
    if a = 0 ∧ b = 0 then
      [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)])]
    else if a = 0 then
      [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)]),
        (Data.B "fake_policyB_hash_28bytes!!!",
        Data.Map [(Data.B "fake_asset_nameB", Data.I b)])]
    else if b = 0 then
      [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)]),
        (Data.B "fake_policyA_hash_28bytes!!!",
        Data.Map [(Data.B "fake_asset_nameA", Data.I a)])]
    else
      [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)]),
        (Data.B "fake_policyA_hash_28bytes!!!",
        Data.Map [(Data.B "fake_asset_nameA", Data.I a)]),
        (Data.B "fake_policyB_hash_28bytes!!!",
        Data.Map [(Data.B "fake_asset_nameB", Data.I b)])]

def spend_sound_theorem
  (validator : ScriptContext → Prop)
  (redeemer : Redeemer)
  (inOrderDatum : OrderDatum)
  (inOrderData : Data)
  (outOrderData : Data)
  : Prop :=
    ∀
      (useStaking : Bool)
      (outAddr : Address)
      (inLovelace inA : Int)         -- input value
      (outLovelace outA outB : Int)  -- output value
      (someSignatory : PubKeyHash)
      -- (someRange : Data)
      ,
    let inStaking := if useStaking then
                        some (.StakingHash (.PubKeyCredential "fake_staking_hash_28bytes!!!"))
                     else
                        none
    let utxo : TxOut :=
      ⟨ ⟨.ScriptCredential "fake_script_hash_28bytes!!!!", inStaking ⟩,
        orderValue inLovelace inA,  -- TODO: can I make this more general?
        .OutputDatum inOrderData,
        none
      ⟩
    let someOutput : TxOut :=
      ⟨ outAddr,
        orderValue2 outLovelace outA outB,  -- TODO: can I make this more general?
        .OutputDatum outOrderData,
        none
      ⟩
    let utxoRef := ⟨"fake_input_txid_32bytes!!!!!!!!!", 0⟩
    let txInfo :=
      { baseTxInfo with
        txInfoInputs := [⟨utxoRef, utxo⟩]
        txInfoOutputs := [someOutput]
        txInfoRedeemers := [(.Spending utxoRef, redeemer)]
        txInfoSignatories := [someSignatory]
        -- txInfoValidRange := someRange
      }
    let ctx : ScriptContext :=
      { scriptContextTxInfo := txInfo
        scriptContextRedeemer := redeemer
        scriptContextScriptInfo := .SpendingScript utxoRef inOrderData
      }
    -- XXX: this is returning false (but is not needed):
    -- validScriptContext ctx ∧
    -- hasInputs ctx [⟨utxoRef, utxo⟩] ∧  -- already covered
    -- constrainedUtxo utxo inValue inOrderData ∧
    inLovelace > 0 ∧
    outLovelace > 0 ∧
    inA ≥ 0 ∧
    outA ≥ 0 ∧
    outB ≥ 0 ∧
    validOrder utxo ∧
    validator ctx
    →
        -- close operation
        someSignatory = inOrderDatum.owner
      ∨
        -- resolve operation
        -- ∃ (contUtxo : TxOut),  contUtxo = someOutput
        (let contUtxo := someOutput
        hasOutputs ctx [contUtxo]
        ∧ validOrder contUtxo
        ∧ validResolve utxo contUtxo inOrderDatum
        )

end Properties.Soundness
