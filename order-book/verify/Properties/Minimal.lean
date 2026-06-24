import Blaster
import Properties.Spec

/-! The compiled *minimal* `order` validator (4-field datum) compared
    against the single specification in `Properties.Spec`. -/

namespace Properties.Minimal

open PlutusCore.UPLC.Term (Program)
open PlutusCore.Data (Data)
open Properties.Spec

set_option warn.sorry false

#import_uplc orderMinimalScript PlutusV3 flat_hex "Scripts/order_minimal_spend.flat"

def orderMinimalValidator : Program := orderMinimalScript.script

def datum : OrderDatum :=
  { owner := "fake_owner_pkh"
    amount := 10
    policyId := "fake_policyB_hash_28bytes!!!"
    assetName := "fake_asset_nameB" }

/-- Unsound: the minimal validator lets the resolver pay the asked asset
    to any address, so acceptance does not imply the continuation stays
    at the script address. -/
theorem spend_unsound :
    ¬ spend_sound_theorem orderMinimalValidator datum (encode4 datum) (encode4 datum)
        (Data.Constr 0 [Data.I 0])
    := by blaster

/-- Complete: a valid resolve is accepted. -/
theorem spend_complete :
    ∀ (datum : OrderDatum),
    spend_complete_theorem orderMinimalValidator datum
      (encode4 datum) (encode4 datum) (Data.Constr 0 [Data.I 0])
    := by blaster

/-- Close is sound: accepted only if the owner signed. -/
theorem close_sound :
    ∀ (datum : OrderDatum),
    close_sound_theorem orderMinimalValidator datum (encode4 datum)
    := by blaster

/-- Close is complete: the owner can spend. -/
theorem close_complete :
    ∀ (datum : OrderDatum),
    close_complete_theorem orderMinimalValidator datum (encode4 datum)
    := by blaster

/-- Does NOT prevent double satisfaction: two inputs can share one
    continuation paying the asset once. -/
theorem double_satisfaction_fails :
    ¬ no_double_satisfaction_theorem orderMinimalValidator datum
        (encode4 datum) (encode4 datum) (Data.Constr 0 [Data.I 0])
    := by blaster

end Properties.Minimal
