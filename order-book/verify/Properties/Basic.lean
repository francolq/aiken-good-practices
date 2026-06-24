import Properties.Complete
import Properties.Vulnerable
import Properties.Minimal
import Properties.MinimalSingle

/-! Aggregator module. Importing this file (or `Properties`, which
    re-exports it) is enough to type-check every theorem in the
    project. Each per-validator module instantiates the shared specs
    from `Properties.Spec`. -/
