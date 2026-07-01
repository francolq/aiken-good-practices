import PlutusCore.UPLC
import CardanoLedgerApi.V3

namespace Properties.Common

open PlutusCore.UPLC.Term (Const)
open PlutusCore.UPLC.CekMachine (State)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-- The CEK machine halted on a value (V3 spending validators return
    unit on success). -/
abbrev accepts (s : State) : Prop := isSuccessful s

/-- The CEK machine errored. -/
abbrev rejects (s : State) : Prop := isUnsuccessful s

/-- The validator run accepted: it halted on unit. `result` is the `State` from
    applying a cached `#prep_uplc` `.prop` to a context. -/
def validatorAccepts (result : State) : Prop :=
  result = .Halt (.VCon Const.Unit)

end Properties.Common
