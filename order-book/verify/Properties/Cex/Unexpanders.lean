import Lean
import CardanoLedgerApi.V3

/-! Unexpanders that prettify a value in the delaborator (layer 3).

    Pair with `elabCexString` (Cex/Bridge.lean), which produces the real value,
    as the `blaster_pretty` tactic does (Cex/Tactic.lean). -/

open Lean PrettyPrinter

namespace Properties.Cex

@[app_unexpander PlutusCore.Data.PlutusCore.DataInternal.Data.Constr]
def unexpandDataConstr : Unexpander
  | `($_ $tag $args) => `(($(mkIdent `Constr) $tag $args))
  | _ => throw ()

@[app_unexpander PlutusCore.Data.PlutusCore.DataInternal.Data.I]
def unexpandDataI : Unexpander
  | `($_ $i) => `($i)
  | _ => throw ()

@[app_unexpander PlutusCore.Data.PlutusCore.DataInternal.Data.B]
def unexpandDataB : Unexpander
  | `($_ $b) => `(($(mkIdent `B) $b))
  | _ => throw ()

partial def collectListElems : Syntax → UnexpandM (List Syntax)
  | `([]) => pure []
  | `(List.cons $h $t) => do
      let tElems ← collectListElems t
      pure (h :: tElems)
  | `(as $inner $_) => collectListElems inner
  | _ => throw ()

def mkCommaSepArray (xs : List Syntax) : Syntax.TSepArray `term "," :=
  { elemsAndSeps := xs.toArray }

@[app_unexpander PlutusCore.Data.PlutusCore.DataInternal.Data.List]
def unexpandDataList : Unexpander
  | `($_ $xs) => do
      let elems ← collectListElems xs
      let arr := mkCommaSepArray elems
      `([$arr,*])
  | _ => throw ()

@[app_unexpander PlutusCore.Data.PlutusCore.DataInternal.Data.Map]
def unexpandDataMap : Unexpander
  | `($_ $kvs) => `(($(mkIdent `Map) $kvs))
  | _ => throw ()

-- Without this, `ByteString.mk ""` prints as the struct `{ data := "" }`.
@[app_unexpander PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk]
def unexpandByteString : Unexpander
  | `($_ $s) => `(($(mkIdent `bytes) $s))
  | _ => throw ()

@[app_unexpander List.cons]
def unexpandListCons : Unexpander
  | `($_ $h $t) => do
      let tElems ← collectListElems t
      let arr := mkCommaSepArray (h :: tElems)
      `([$arr,*])
  | _ => throw ()

@[app_unexpander List.nil]
def unexpandListNil : Unexpander
  | `($_) => `([])

end Properties.Cex
