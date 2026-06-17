import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster
import Properties.Common
import Properties.Order.Complete.Spec
import Properties.Order.Vulnerable.Completeness

/-! The vulnerable validator fails to prevent double-satisfaction. -/

namespace Properties.Order.Vulnerable.DoubleSatisfaction

open Properties.Common (validatorAccepts)
open Properties.Order.Complete.Spec (noDoubleSatisfaction)
open Properties.Order.Vulnerable.Completeness (orderVulnerableValidator)

set_option warn.sorry false

theorem no_double_satisfaction_fails :
    ¬ noDoubleSatisfaction (validatorAccepts · orderVulnerableValidator)
    := by blaster

end Properties.Order.Vulnerable.DoubleSatisfaction
