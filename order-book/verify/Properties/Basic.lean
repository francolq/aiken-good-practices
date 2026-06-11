import Properties.Order.Complete.Validator
import Properties.Order.Complete.MintValidator
import Properties.Order.Complete.Soundness
import Properties.Order.Complete.DoubleSatisfaction
import Properties.Order.Vulnerable.Validator
import Properties.Order.Vulnerable.Soundness
import Properties.Order.Vulnerable.DoubleSatisfaction
import Properties.Order.Minimal.Validator
import Properties.Order.Minimal.Soundness
import Properties.Order.Minimal.DoubleSatisfaction
import Properties.Order.MinimalSingle.Validator
import Properties.Order.MinimalSingle.Soundness
import Properties.Order.MinimalSingle.DoubleSatisfaction

/-! Aggregator module. Importing this file (or `Properties`, which
    re-exports it) is enough to type-check every theorem in the
    project. -/
