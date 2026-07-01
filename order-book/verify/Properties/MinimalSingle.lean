import Blaster
import Properties.Spec
import Properties.Prep

/-! The compiled *minimal-single-input* `order` validator compared
    against the single specification in `Properties.Spec`. The
    single-input restriction prevents double-satisfaction but does not
    constrain the continuation. -/

namespace Properties.MinimalSingle

open PlutusCore.Data (Data)
open Properties.Spec

set_option warn.sorry false

def datum : OrderDatum :=
  { owner := "fake_owner_pkh"
    amount := 10
    policyId := "fake_policyB_hash_28bytes!!!"
    assetName := "fake_asset_nameB" }

/-- Unsound: the single-input restriction only blocks double-satisfaction;
    the resolver can still pay the asked asset to any address. -/
theorem spend_unsound :
    ¬ spend_sound_theorem msiResolve.prop datum
        (encode4 datum) (encode4 datum) (Data.Constr 0 [Data.I 0])
    := by blaster

/-- Complete: a valid resolve is accepted. -/
theorem spend_complete :
    ∀ (datum : OrderDatum),
    spend_complete_theorem msiResolve.prop datum
      (encode4 datum) (encode4 datum) (Data.Constr 0 [Data.I 0])
    := by blaster

/-- Close is sound: accepted only if the owner signed. -/
theorem close_sound :
    ∀ (datum : OrderDatum),
    close_sound_theorem msiClose.prop datum (encode4 datum)
    := by blaster

/-- Close is complete: the owner can spend. -/
theorem close_complete :
    ∀ (datum : OrderDatum),
    close_complete_theorem msiClose.prop datum (encode4 datum)
    := by blaster

/-- Prevents double satisfaction: requiring exactly one input at the
    script address rules out two-input transactions. -/
theorem no_double_satisfaction :
    ∀ (datum : OrderDatum) (contDatumData : Data) (redeemer : CardanoLedgerApi.V3.Redeemer),
    no_double_satisfaction_theorem msiNoDsat.prop datum
      (encode4 datum) contDatumData redeemer
    := by blaster

end Properties.MinimalSingle
