import Blaster
import Properties.Soundness

namespace Properties.OrderV1

open PlutusCore.UPLC.Term (Program)
open Properties.Soundness (spend_sound_theorem)

set_option warn.sorry false

#import_uplc orderV1Script PlutusV3 flat_hex "Scripts/order_v1_spend.flat"

def orderV1Validator : Program := orderV1Script.script

theorem spend_sound :
  spend_sound_theorem orderV1Validator
  := by blaster

end Properties.OrderV1
