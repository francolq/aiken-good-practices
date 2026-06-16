import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Order.Common
import Properties.Order.Complete.Completeness

/-! Double-satisfaction prevention for the complete validator. -/

namespace Properties.Order.Complete.DoubleSatisfaction

open Properties.Order.Common (noDoubleSatisfaction)
open Properties.Order.Complete.Completeness (orderAcceptsProp)

set_option warn.sorry false

theorem no_double_satisfaction : noDoubleSatisfaction orderAcceptsProp
    := by blaster

end Properties.Order.Complete.DoubleSatisfaction
