import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Order.Common
import Properties.Order.Vulnerable.Completeness

/-! The vulnerable validator fails to prevent double-satisfaction. -/

namespace Properties.Order.Vulnerable.DoubleSatisfaction

open Properties.Order.Common (noDoubleSatisfaction)
open Properties.Order.Vulnerable.Completeness (orderVulnerableAcceptsProp)

set_option warn.sorry false

theorem no_double_satisfaction_fails :
    ¬ noDoubleSatisfaction orderVulnerableAcceptsProp
    := by blaster

end Properties.Order.Vulnerable.DoubleSatisfaction
