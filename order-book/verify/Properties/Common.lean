import PlutusCore.UPLC
import CardanoLedgerApi

namespace Properties.Common

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext spendingInputs)
open PlutusCore.UPLC.Term (Const Program)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram State)
open PlutusCore.UPLC.Utils (isSuccessful)

def validatorAccepts (ctx : ScriptContext) (validator : Program) : Prop :=
  cekExecuteProgram validator (spendingInputs ctx) 5000
    = .Halt (.VCon Const.Unit)

def validatorAccepts2
     (ctx : ScriptContext)
     (validator : ScriptContext → State) : Prop :=
  isSuccessful (validator ctx)


end Properties.Common
