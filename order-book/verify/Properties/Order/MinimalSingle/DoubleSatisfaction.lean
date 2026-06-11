import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Order.Minimal.DoubleSatisfaction
import Properties.Order.MinimalSingle.Validator

/-! The single-input restriction prevents double-satisfaction. -/

namespace Properties.Order.MinimalSingle.DoubleSatisfaction

open Properties.Order.Minimal.DoubleSatisfaction (noDoubleSatisfaction)
open Properties.Order.MinimalSingle.Validator (orderMinimalSingleAcceptsProp)

set_option warn.sorry false

theorem no_double_satisfaction :
    noDoubleSatisfaction orderMinimalSingleAcceptsProp
    := by blaster

end Properties.Order.MinimalSingle.DoubleSatisfaction
