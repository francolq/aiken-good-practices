import Blaster
import Properties.Spec
import Properties.Prep

/-! The compiled *vulnerable* `order` validator compared against the
    single specification in `Properties.Spec`. Its `Resolve` branch
    checks `tag == None` instead of `tag == Some(own_ref)`. -/

namespace Properties.Vulnerable

open PlutusCore.Data (Data)
open Properties.Spec

set_option warn.sorry false

def datum : OrderDatum :=
  { owner := "fake_owner_pkh"
    amount := 10
    policyId := "fake_policyB_hash_28bytes!!!"
    assetName := "fake_asset_nameB" }

/-- Sound (for a single transaction): like the complete validator, the
    continuation must stay at the script address and pay the asked asset.
    The continuation datum keeps `tag := None`. (Its weakness is
    double-satisfaction across transactions, not single-tx soundness.) -/
theorem spend_sound :
    ∀ (datum : OrderDatum) (inTag : Option CardanoLedgerApi.V3.TxOutRef) (idx : Int),
    spend_sound_theorem vResolve.prop datum
      (encode5 datum inTag) (encode5 datum none)
      (Data.Constr 0 [Data.I idx])
    := by blaster

/-- Complete: a valid resolve is accepted. -/
theorem spend_complete :
    ∀ (datum : OrderDatum) (inTag : Option CardanoLedgerApi.V3.TxOutRef),
    spend_complete_theorem vResolve.prop datum
      (encode5 datum inTag) (encode5 datum none)
      (Data.Constr 0 [Data.I 0])
    := by blaster

/-- Close is sound: accepted only if the owner signed. -/
theorem close_sound :
    ∀ (datum : OrderDatum) (inTag : Option CardanoLedgerApi.V3.TxOutRef),
    close_sound_theorem vClose.prop datum (encode5 datum inTag)
    := by blaster

/-- Close is complete: the owner can spend (sign + burn). -/
theorem close_complete :
    ∀ (datum : OrderDatum) (inTag : Option CardanoLedgerApi.V3.TxOutRef),
    close_complete_theorem vClose.prop datum (encode5 datum inTag)
    := by blaster

/-- Does NOT prevent double satisfaction: the continuation datum carries
    `tag := None` (not bound to an input), so a single continuation
    satisfies two distinct inputs. -/
theorem double_satisfaction_fails :
    ¬ no_double_satisfaction_theorem vNoDsat.prop datum
        (encode5 datum none) (encode5 datum none) (Data.Constr 0 [Data.I 0])
    := by blaster

/-! ### Minting policy (same as the complete validator) -/

theorem mint_complete :
    mint_complete_theorem vMint.prop (encode5 datum none) := by blaster

theorem mint_sound :
    mint_sound_theorem vMint.prop (encode5 datum none) := by blaster

theorem burn_complete : burn_complete_theorem vBurn.prop := by blaster

theorem burn_sound : burn_sound_theorem vBurn.prop := by blaster

end Properties.Vulnerable
