import PlutusCore.UPLC

namespace Properties.Common

open PlutusCore.UPLC.CekMachine (State)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-- The CEK machine halted on a value (V3 spending validators return
    unit on success). -/
abbrev accepts (s : State) : Prop := isSuccessful s

/-- The CEK machine errored. -/
abbrev rejects (s : State) : Prop := isUnsuccessful s

end Properties.Common
