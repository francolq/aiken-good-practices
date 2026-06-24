import Blaster
import Properties.Spec

/-! The compiled *complete* `order` validator (5-field datum with `tag`)
    compared against the single specification in `Properties.Spec`. -/

namespace Properties.Complete

open PlutusCore.UPLC.Term (Program)
open PlutusCore.Data (Data)
open Properties.Spec

set_option warn.sorry false

#import_uplc orderScript PlutusV3 flat_hex "Scripts/order_spend.flat"
#import_uplc orderMintScript PlutusV3 flat_hex "Scripts/order_mint.flat"

def orderValidator : Program := orderScript.script
def orderMintValidator : Program := orderMintScript.script

def datum : OrderDatum :=
  { owner := "fake_owner_pkh"
    amount := 10
    policyId := "fake_policyB_hash_28bytes!!!"
    assetName := "fake_asset_nameB" }

/-- Sound: the complete validator forces the continuation to stay at the
    script address and pay the asked asset. The continuation datum keeps
    owner/asset/amount and sets `tag := Some own_ref`. -/
theorem spend_sound :
    ∀ (datum : OrderDatum) (inTag : Option CardanoLedgerApi.V3.TxOutRef) (idx : Int),
    spend_sound_theorem orderValidator datum
      (encode5 datum inTag) (encode5 datum (some orderRef))
      (Data.Constr 0 [Data.I idx])
    := by blaster

/-- Complete: a valid resolve is accepted. -/
theorem spend_complete :
    ∀ (datum : OrderDatum) (inTag : Option CardanoLedgerApi.V3.TxOutRef),
    spend_complete_theorem orderValidator datum
      (encode5 datum inTag) (encode5 datum (some orderRef))
      (Data.Constr 0 [Data.I 0])
    := by blaster

/-- Close is sound: accepted only if the owner signed. -/
theorem close_sound :
    ∀ (datum : OrderDatum) (inTag : Option CardanoLedgerApi.V3.TxOutRef),
    close_sound_theorem orderValidator datum (encode5 datum inTag)
    := by blaster

/-- Close is complete: the owner can spend (sign + burn). -/
theorem close_complete :
    ∀ (datum : OrderDatum) (inTag : Option CardanoLedgerApi.V3.TxOutRef),
    close_complete_theorem orderValidator datum (encode5 datum inTag)
    := by blaster

/-- Prevents double satisfaction: the `tag = Some own_ref` binding means
    one continuation cannot satisfy two distinct inputs. -/
theorem no_double_satisfaction :
    ∀ (datum : OrderDatum) (inTag : Option CardanoLedgerApi.V3.TxOutRef)
      (contDatumData : Data) (redeemer : CardanoLedgerApi.V3.Redeemer),
    no_double_satisfaction_theorem orderValidator datum
      (encode5 datum inTag) contDatumData redeemer
    := by blaster

/-! ### Minting policy -/

theorem mint_complete :
    mint_complete_theorem orderMintValidator (encode5 datum none) := by blaster

theorem mint_sound :
    mint_sound_theorem orderMintValidator (encode5 datum none) := by blaster

theorem burn_complete : burn_complete_theorem orderMintValidator := by blaster

theorem burn_sound : burn_sound_theorem orderMintValidator := by blaster

end Properties.Complete
