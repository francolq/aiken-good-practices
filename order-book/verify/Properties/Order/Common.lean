import CardanoLedgerApi.V3

/-! Helpers and encodings shared by every order validator variant
    (`Minimal`, `MinimalSingle`, `Complete`, `Vulnerable`). -/

namespace Properties.Order.Common

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open CardanoLedgerApi.V3 (Address Value)

def scriptAddr (h : ByteString) : Address :=
  { addressCredential := .ScriptCredential h
    addressStakingCredential := none }

/-- Spend-redeemer ADT mirroring `OrderRedeemer` in `order.ak`. -/
inductive RedeemerKind
  | Resolve (outIx : Int)
  | Close

def redeemerKindData : RedeemerKind → Data
  | .Resolve n => Data.Constr 0 [Data.I n]
  | .Close     => Data.Constr 1 []

/-- Three-entry value carried by a script input: ada plus two arbitrary
    tokens. Shared by every input across all order validators. -/
structure InputValue where
  lovelace : Int
  policy1  : ByteString
  asset1   : ByteString
  qty1     : Int
  policy2  : ByteString
  asset2   : ByteString
  qty2     : Int

def inputValueToValue (iv : InputValue) : Value :=
  [(Data.B "", Data.Map [(Data.B "", Data.I iv.lovelace)]),
   (Data.B iv.policy1, Data.Map [(Data.B iv.asset1, Data.I iv.qty1)]),
   (Data.B iv.policy2, Data.Map [(Data.B iv.asset2, Data.I iv.qty2)])]

end Properties.Order.Common
