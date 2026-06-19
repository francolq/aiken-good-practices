import Blaster
import Properties.Soundness

namespace Properties.OrderV2

open PlutusCore.UPLC.Term (Program)
open Properties.Soundness (spend_sound_theorem)

set_option warn.sorry false

#import_uplc orderV2Script PlutusV3 flat_hex "Scripts/order_v2_spend.flat"

def orderV2Validator : Program := orderV2Script.script

theorem spend_sound :
  spend_sound_theorem orderV2Validator
  := by blaster

end Properties.OrderV2
