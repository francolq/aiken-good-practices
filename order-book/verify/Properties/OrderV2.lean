import Blaster
import Properties.Soundness

namespace Properties.OrderV2

open PlutusCore.UPLC.Term (Program)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (ScriptContext Redeemer TxOutRef spendingInputs)
open Properties.Common (validatorAccepts validatorAccepts2)
open Properties.Soundness (OrderDatum spend_sound_theorem)

set_option warn.sorry false

#import_uplc orderV2Script PlutusV3 flat_hex "Scripts/order_v2_spend.flat"

#prep_uplc appliedOrderV2Script orderV2Script spendingInputs 1

def tagData : Option TxOutRef → Data
  | none     => Data.Constr 1 []
  | some ref => Data.Constr 0 [IsData.toData ref]

def orderData (tag : Option TxOutRef) (d : OrderDatum) : Data :=
  Data.Constr 0
  [ Data.B d.owner,
    Data.I d.amount,
    Data.B d.policyId,
    Data.B d.assetName,
    tagData tag ]

def orderV2Validator (ctx : ScriptContext) : Prop :=
  validatorAccepts ctx orderV2Script.script

def orderV2Validator2 (ctx : ScriptContext) : Prop :=
  validatorAccepts2 ctx appliedOrderV2Script.prop

theorem spend_sound :
  ∀ (redeemer : Redeemer)
    (tag : Option TxOutRef),
  -- let redeemer : Redeemer := Data.Constr 0 [Data.I idx]
  -- let tag := none
  spend_sound_theorem orderV2Validator redeemer (orderData tag)
  -- spend_sound_theorem orderV2Validator2 redeemer (orderData tag)
  := by blaster

end Properties.OrderV2
