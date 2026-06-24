import Blaster
import Properties.Soundness

namespace Properties.OrderV2

open PlutusCore.UPLC.Term (Program)
open PlutusCore.Data (Data)
open CardanoLedgerApi.V3 (Redeemer)
open Properties.Soundness (spend_sound_theorem)

set_option warn.sorry false

#import_uplc orderV2Script PlutusV3 flat_hex "Scripts/order_v2_spend.flat"

def orderV2Validator : Program := orderV2Script.script

theorem spend_sound :
  ∀ (redeemer : Redeemer),
  -- let redeemer : Redeemer := Data.Constr 0 [Data.I idx]
  spend_sound_theorem orderV2Validator redeemer
  := by blaster

end Properties.OrderV2
