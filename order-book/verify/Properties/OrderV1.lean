import Blaster
import Properties.Soundness

namespace Properties.OrderV1

open PlutusCore.UPLC.Term (Program)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.V3 (ScriptContext Redeemer spendingInputs)
open Properties.Common (validatorAccepts validatorAccepts2)
open Properties.Soundness (OrderDatum spend_sound_theorem)

set_option warn.sorry false

#import_uplc orderV1Script PlutusV3 flat_hex "Scripts/order_v1_spend.flat"

#prep_uplc appliedOrderV1Script orderV1Script spendingInputs 1

#print orderV1Script

-- steps = 500 we get something empty: fun ctx => PlutusCore.UPLC.CekMachine.State.Error,
-- steps = 600 we get something longer: ~70 lines
-- steps = 1000 we get something even longer
-- steps = 1500 still not finding the counterexample (+40 seconds)
-- steps = 1600 still not finding the counterexample (+100 seconds)
-- steps = 1700 still not finding the counterexample (+270 seconds)
-- steps = 1800 still not finding the counterexample (+700 seconds)
#print appliedOrderV1Script

def orderData (d : OrderDatum) : Data :=
  Data.Constr 0
  [ Data.B d.owner,
    Data.I d.amount,
    Data.B d.policyId,
    Data.B d.assetName ]

def orderV1Validator (ctx : ScriptContext) : Prop :=
  validatorAccepts ctx orderV1Script.script

def orderV1Validator2 (ctx : ScriptContext) : Prop :=
  validatorAccepts2 ctx appliedOrderV1Script.prop

theorem spend_sound :
  ∀ (redeemer : Redeemer),
  -- let redeemer : Redeemer := Data.Constr 0 []
  spend_sound_theorem orderV1Validator redeemer orderData
  -- spend_sound_theorem orderV1Validator2 redeemer orderData
  := by blaster

end Properties.OrderV1
