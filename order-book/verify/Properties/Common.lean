import PlutusCore.UPLC
import CardanoLedgerApi

namespace Properties.Common

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext)
open PlutusCore.UPLC.Term (Const Program)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)

def validatorAccepts (ctx : ScriptContext) (validator : Program) : Prop :=
  cekExecuteProgram validator [toTerm ctx] 5000
    = .Halt (.VCon Const.Unit)

end Properties.Common
