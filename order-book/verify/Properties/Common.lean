import PlutusCore.UPLC
import CardanoLedgerApi.V3

namespace Properties.Common

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext)
open PlutusCore.UPLC.Term (Const Program)
open PlutusCore.UPLC.CekMachine (State cekExecuteProgram)
open PlutusCore.UPLC.Utils (isSuccessful isUnsuccessful)

/-- The CEK machine halted on a value (V3 spending validators return
    unit on success). -/
abbrev accepts (s : State) : Prop := isSuccessful s

/-- The CEK machine errored. -/
abbrev rejects (s : State) : Prop := isUnsuccessful s

/-- The compiled `validator` accepts `ctx`. -/
def validatorAccepts (ctx : ScriptContext) (validator : Program) : Prop :=
  cekExecuteProgram validator [toTerm ctx] 5000000
    = .Halt (.VCon Const.Unit)

end Properties.Common
