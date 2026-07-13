/-! Cleans a raw z3 counterexample string into readable text (layer 1).

    z3 returns the model as an s-expression whose names are already Lean
    qualified. Three noises separate that from a Lean value, all handled here:
      1. `(let ((a!N v) ...) body)`       z3 sharing, inlined
      2. `(as Option.none (@Option @X))`  type ascriptions, dropped
      3. huge qualified names             shortened

    `prettyCex` does it as pure text, no elaboration and no deps, for any Blaster
    cex. `prettyFull` keeps full names so the result is well-formed Lean, ready
    for the bridge (see Cex/Bridge.lean). -/

namespace Properties.Cex

inductive SExp where
  | atom : String → SExp
  | list : List SExp → SExp
deriving Inhabited

partial def readString : List Char → String → String × List Char
  | [], acc => (acc, [])
  | c :: rest, acc => if c == '"' then (acc.push '"', rest) else readString rest (acc.push c)

partial def tokenize : List Char → String → List String → List String
  | [], cur, acc => (if cur.isEmpty then acc else cur :: acc).reverse
  | c :: rest, cur, acc =>
    let flush := if cur.isEmpty then acc else cur :: acc
    if c == '"' then
      let (lit, rest') := readString rest "\""
      tokenize rest' "" (lit :: flush)
    else if c == '(' || c == ')' then
      tokenize rest "" (c.toString :: flush)
    else if c == ' ' || c == '\n' || c == '\t' || c == '\r' then
      tokenize rest "" flush
    else
      tokenize rest (cur.push c) acc

mutual
  partial def parseOne : List String → SExp × List String
    | "(" :: rest => parseSeq rest []
    | t :: rest   => (SExp.atom t, rest)
    | []          => (SExp.atom "", [])
  partial def parseSeq : List String → List SExp → SExp × List String
    | ")" :: rest, acc => (SExp.list acc.reverse, rest)
    | [], acc          => (SExp.list acc.reverse, [])
    | toks, acc        => let (e, rest) := parseOne toks; parseSeq rest (e :: acc)
end

/-- Drops `(as x _)` and inlines the z3 `let`s. -/
partial def clean (env : List (String × SExp)) : SExp → SExp
  | .atom a => (env.lookup a).getD (.atom a)
  | .list [.atom "as", x, _ty] => clean env x
  | .list [.atom "let", .list binds, body] =>
      let env' := binds.foldl (fun e b =>
        match b with
        | .list [.atom name, val] => (name, clean e val) :: e
        | _ => e) env
      clean env' body
  | .list xs => .list (xs.map (clean env))

/-- Shortens a qualified name to its last two components. -/
def shorten (a : String) : String :=
  if a.startsWith "\"" then a
  else match a.splitOn "." |>.reverse with
    | "none" :: _ => "none"
    | "nil"  :: _ => "[]"
    | last :: prev :: _ => prev ++ "." ++ last
    | _ => a

partial def flat : SExp → String
  | .atom a  => shorten a
  | .list xs => "(" ++ String.intercalate " " (xs.map flat) ++ ")"

def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '\''

/-- Copies a `"..."` literal verbatim (honoring `\`), closing quote included. -/
partial def copyString : List Char → String → String × List Char
  | [], acc => (acc, [])
  | '\\' :: c :: rest, acc => copyString rest ((acc.push '\\').push c)
  | '"' :: rest, acc => (acc.push '"', rest)
  | c :: rest, acc => copyString rest (acc.push c)

/-- Like `shorten` but keeps only the last component (the bare constructor).
    `CardanoLedgerApi.V1.Credential.Credential.ScriptCredential` becomes `ScriptCredential`. -/
def shortenTail (a : String) : String :=
  if a.startsWith "\"" then a
  else match a.splitOn "." |>.reverse with
    | "none" :: _ => "none"
    | "nil"  :: _ => "[]"
    | last :: _   => last
    | _ => a

/-- Shortens qualified names inside an already-formatted string (e.g. `ppExpr`
    output), leaving string literals intact. Each dotted token keeps its last
    component only. -/
partial def shortenNames (input : String) : String :=
  let shortenTok (t : String) : String := if t.isEmpty then "" else shortenTail t
  let rec go : List Char → String → String → String
    | [], cur, acc => acc ++ shortenTok cur
    | '"' :: rest, cur, acc =>
        let (lit, rest') := copyString rest "\""
        go rest' "" (acc ++ shortenTok cur ++ lit)
    | c :: rest, cur, acc =>
        if isIdentChar c then go rest (cur.push c) acc
        else go rest "" (acc ++ shortenTok cur ++ c.toString)
  go input.toList "" ""

/-- Renders with indentation: inline if it fits, split across lines if large. -/
partial def render (ind : Nat) (s : SExp) : String :=
  let f := flat s
  if f.length ≤ 72 then f
  else match s with
    | .atom a => shorten a
    | .list [] => "()"
    | .list (h :: rest) =>
        let pad := "".pushn ' ' (ind + 2)
        let body := rest.map (fun c => pad ++ render (ind + 2) c)
        "(" ++ flat h ++ "\n" ++ String.intercalate "\n" body ++ ")"

/-- Entry point: raw text of one cex value in, readable text out. -/
def prettyCex (input : String) : String :=
  render 0 (clean [] (parseOne (tokenize input.toList "" [])).1)

partial def flatFull : SExp → String
  | .atom a  => a
  | .list xs => "(" ++ String.intercalate " " (xs.map flatFull) ++ ")"

/-- Same cleanup as `prettyCex` but keeps full names, so the result is
    well-formed Lean ready to elaborate. -/
def prettyFull (input : String) : String :=
  flatFull (clean [] (parseOne (tokenize input.toList "" [])).1)

end Properties.Cex
