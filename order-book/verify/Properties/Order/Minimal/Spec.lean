import CardanoLedgerApi.V3
import CardanoLedgerApi.V1.Contexts
import Properties.Order.Common

/-! Pure Lean specification for the minimal `order` validator. No
    anti-double-satisfaction tag and no validity token: the datum has
    four fields and the continuation value carries only ada and the
    requested asset. -/

namespace Properties.Order.Minimal.Spec

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open CardanoLedgerApi.V3 (Address TxOutRef Value)
open Properties.Order.Common (scriptAddr)

structure Datum where
  owner     : ByteString
  amount    : Int
  policyId  : ByteString
  assetName : ByteString

def datumData (d : Datum) : Data :=
  Data.Constr 0
    [Data.B d.owner, Data.I d.amount, Data.B d.policyId, Data.B d.assetName]

/-- Continuation value: ada plus the requested asset. No `val` token. -/
def twoEntryValue (lovelace : Int) (policyId assetName : ByteString)
    (assetAmount : Int) : Value :=
  [(Data.B "", Data.Map [(Data.B "", Data.I lovelace)]),
   (Data.B policyId, Data.Map [(Data.B assetName, Data.I assetAmount)])]

def wellFormedResolveValue
    (lovelace : Int) (policyId assetName : ByteString)
    (assetAmount : Int) : Prop :=
  CardanoLedgerApi.V1.Contexts.validTxOutValue
    (twoEntryValue lovelace policyId assetName assetAmount) = true

structure ResolveInput where
  ref      : TxOutRef
  datum    : Datum
  lovelace : Int

structure ResolveContinuation where
  address     : Address
  datum       : Datum
  lovelace    : Int
  assetAmount : Int

structure CloseInput where
  ref   : TxOutRef
  datum : Datum

/-- Resolve spec: some output pays at least `amount` of the requested
    asset. No address or datum constraint. -/
def validResolve
    (input : ResolveInput) (cont : ResolveContinuation) : Prop :=
  cont.assetAmount ≥ input.datum.amount

/-- Close spec: the signer matches the input datum's owner. -/
def validClose (input : CloseInput) (signer : ByteString) : Prop :=
  signer = input.datum.owner

end Properties.Order.Minimal.Spec
