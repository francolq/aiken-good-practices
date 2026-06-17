import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Common
import Properties.Order.Minimal.DoubleSatisfaction
import Properties.Order.MinimalSingle.Completeness

/-! The single-input restriction prevents double-satisfaction. -/

namespace Properties.Order.MinimalSingle.DoubleSatisfaction

open Properties.Common (validatorAccepts)
open Properties.Order.Minimal.DoubleSatisfaction (noDoubleSatisfaction)
open Properties.Order.MinimalSingle.Completeness (orderMinimalSingleValidator)

set_option warn.sorry false

theorem no_double_satisfaction :
    noDoubleSatisfaction (validatorAccepts · orderMinimalSingleValidator)
    := by blaster

end Properties.Order.MinimalSingle.DoubleSatisfaction
