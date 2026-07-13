import Lean
import Blaster
import Properties.Cex.Pretty
import Properties.Cex.Bridge
import Properties.Cex.Unexpanders

/-! The `blaster_pretty` tactic: a drop-in for `by blaster` that, on a falsified
    goal, shows the cex already cleaned in the error.

    Mechanics: it runs the same pipeline as `blaster` (`Translate.main` returns
    `Result.Falsified cex`), drops the raw cex Blaster logged from the message log,
    and rethrows with the pretty version. Valid/Undetermined behave like `blaster`.

    The body is a copy of `blaster`'s own `blasterTacticImp` -/

open Lean Elab Tactic Meta
open Blaster.Optimize Blaster.Smt Blaster.Options Blaster.Syntax

namespace Properties.Cex

syntax (name := blasterPretty) "blaster_pretty" (solveOption)* : tactic

@[tactic blasterPretty]
def blasterPrettyImp : Tactic := fun stx =>
  withMainContext do
    let opts := stx[1].getArgs
    let sOpts ← parseSolveOptions opts default
    let goal ← revertHyps (← getMainGoal)
    let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
    -- snapshot the message log before running, to drop the raw cex afterwards
    let msgsBefore := (← getThe Core.State).messages
    let ((result, optExpr), _) ←
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) do
        IO.setNumHeartbeats 0
        Translate.main (← goal.getType) (logUndetermined := false) |>.run env
    match result with
    | .Valid => goal.admit -- TODO: proof reconstruction, like blaster
    | .Falsified cex =>
        -- `dropRight 1` strips the trailing char, as Blaster's own dumpCex does
        let rendered ← cex.mapM fun s => renderEntry (s.dropRight 1)
        -- drop everything logged (raw cex plus any elaboration logs), then rethrow
        modifyThe Core.State fun st => { st with messages := msgsBefore }
        throwError "❌ Goal falsified. Counterexample:\n\n{"\n\n".intercalate rendered}"
    | .Undetermined =>
        let newGoal ← goal.replaceTargetDefEq optExpr
        replaceMainGoal [newGoal]
where
  /-- Renders one `name: value` cex entry: elaborates the value into a real Expr
      and prints it with `ppExpr` (named fields plus unexpanders), falling back to
      plain text if elaboration fails. -/
  renderEntry (line : String) : TacticM String := do
    let (name, valStr) :=
      match line.splitOn ": " with
      | n :: rest => (n, ": ".intercalate rest)
      | []        => ("", line)
    try
      let e ← Properties.Cex.elabCexString valStr
      return s!"{name}:\n{Properties.Cex.shortenNames (← ppExpr e).pretty}"
    catch _ =>
      return s!"{name}:\n{Properties.Cex.prettyCex valStr}"

  /-- Reverts the propositional hypotheses into the goal (same as blaster's helper). -/
  revertHyps (goal : MVarId) : TacticM MVarId :=
    goal.withContext do
      let lctx ← getLCtx
      let mut hyps := #[]
      for decl in lctx do
        if decl.isImplementationDetail then continue
        if ← isProp decl.type then
          hyps := hyps.push decl.fvarId
      hyps.foldrM (fun h g => do let (_, g) ← g.revert #[h]; return g) goal

end Properties.Cex
