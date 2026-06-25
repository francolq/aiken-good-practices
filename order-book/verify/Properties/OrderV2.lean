import Blaster
import Properties.Soundness

namespace Properties.OrderV2

open PlutusCore.UPLC.Term (Program)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.IsData.Class (IsData)
open CardanoLedgerApi.V3 (Redeemer TxOutRef)
open Properties.Soundness (OrderDatum spend_sound_theorem)

set_option warn.sorry false

#import_uplc orderV2Script PlutusV3 flat_hex "Scripts/order_v2_spend.flat"

def orderV2Validator : Program := orderV2Script.script

def tagData : Option TxOutRef → Data
  | none     => Data.Constr 1 []
  | some ref => Data.Constr 0 [IsData.toData ref]

def orderData (tag : Option TxOutRef) (d : OrderDatum) : Data :=
  Data.Constr 0
  [ Data.B d.owner,
    Data.I d.amount,
    Data.B d.policyId,
    Data.B d.assetName,
    tagData tag ]

theorem spend_sound :
  ∀ (redeemer : Redeemer)
    (tag : Option TxOutRef),
  -- let redeemer : Redeemer := Data.Constr 0 [Data.I idx]
  -- let tag := none
  spend_sound_theorem orderV2Validator redeemer (orderData tag)
  := by blaster

end Properties.OrderV2
