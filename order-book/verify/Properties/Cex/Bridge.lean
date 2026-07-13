import Lean
import CardanoLedgerApi.V3
import Properties.Cex.Pretty

/-! Bridges a raw z3 cex string to a real Lean value (layer 2).

    `elabCexString "<raw z3 text>"` cleans the string with `prettyFull`, parses it
    as a term and elaborates it. The result is a genuine `ScriptContext` (or
    `TxOutRef`, `Redeemer`, ...), so from there everything on the value side works:
    `repr`, `ToString`, unexpanders (see Cex/Unexpanders.lean). Used by the
    `blaster_pretty` tactic (see Cex/Tactic.lean). -/

open Lean Elab Term

namespace Properties.Cex

/-- Takes the raw text of ONE cex variable (what follows `utxoRef:`, `ctx:`, ...)
    and elaborates it into the Lean value. Used by the `blaster_pretty` tactic. -/
def elabCexString (raw : String) : TermElabM Expr := do
  let cleaned := Properties.Cex.prettyFull raw
  match Lean.Parser.runParserCategory (← getEnv) `term cleaned with
  | .error e  => throwError "failed to parse the cleaned cex expression:\n{e}\n\nExpression:\n{cleaned}"
  | .ok stx   => instantiateMVars (← elabTermAndSynthesize stx none)

end Properties.Cex
