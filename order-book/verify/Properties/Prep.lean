import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Properties.Spec

/-! Pre-reduces each compiled validator against the fixed-shape context
    conversion functions from `Properties.Spec`, caching the residual `.prop` in
    this module's `.olean`. Theorem modules run the validator via these `.prop`s
    instead of `cekExecuteProgram`. Kept separate so editing a theorem never
    reruns the prep.

    `#prep_uplc` registers names at the root namespace, so they are prefixed per
    validator (`m`/`msi`/`c`/`v`) to stay unique. -/

open Properties.Spec (resolveInputs closeInputs noDsatInputs mintInputs burnInputs)

#import_uplc orderMinimalScript PlutusV3 flat_hex "Scripts/order_minimal_spend.flat"
#import_uplc orderMinimalSingleScript PlutusV3 flat_hex "Scripts/order_minimal_single_spend.flat"
#import_uplc orderScript PlutusV3 flat_hex "Scripts/order_spend.flat"
#import_uplc orderMintScript PlutusV3 flat_hex "Scripts/order_mint.flat"
#import_uplc orderVulnerableScript PlutusV3 flat_hex "Scripts/order_vulnerable_spend.flat"
#import_uplc orderVulnerableMintScript PlutusV3 flat_hex "Scripts/order_vulnerable_mint.flat"

#prep_uplc mResolve orderMinimalScript resolveInputs 5000
#prep_uplc mClose orderMinimalScript closeInputs 5000
#prep_uplc mNoDsat orderMinimalScript noDsatInputs 5000

#prep_uplc msiResolve orderMinimalSingleScript resolveInputs 5000
#prep_uplc msiClose orderMinimalSingleScript closeInputs 5000
#prep_uplc msiNoDsat orderMinimalSingleScript noDsatInputs 5000

#prep_uplc cResolve orderScript resolveInputs 5000
#prep_uplc cClose orderScript closeInputs 5000
#prep_uplc cNoDsat orderScript noDsatInputs 5000
#prep_uplc cMint orderMintScript mintInputs 5000
#prep_uplc cBurn orderMintScript burnInputs 5000

#prep_uplc vResolve orderVulnerableScript resolveInputs 5000
#prep_uplc vClose orderVulnerableScript closeInputs 5000
#prep_uplc vNoDsat orderVulnerableScript noDsatInputs 5000
#prep_uplc vMint orderVulnerableMintScript mintInputs 5000
#prep_uplc vBurn orderVulnerableMintScript burnInputs 5000
