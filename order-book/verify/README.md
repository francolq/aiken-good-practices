# Properties

Lean 4 / Blaster proofs about the compiled UPLC of the `order` validators.

## Architecture

Each property is a single `def <name>_theorem (validator : Program) ... : Prop`
in `Properties/Spec.lean`, with the `ScriptContext` built **inline**; the
theorem _is_ the spec. There is one specification; every validator is compared
against it. The only parameters are `validator` plus the **values** that depend
on it (the datum and its on-chain encoding, the continuation datum, a redeemer).

- `Properties/Spec.lean`: the single specification module.
- `Properties/{Complete,Vulnerable,Minimal,MinimalSingle}.lean`: one
  module per validator, loading its `.flat` and instantiating each property
  with `:= by blaster`, using `¬` where the validator fails it.
- `Properties/Common.lean`: `validatorAccepts`.
- `Properties/Basic.lean`: aggregator (imports the four).

## Results (28 theorems)

| Property                 | Complete | Vulnerable | Minimal | MinimalSingle |
| ------------------------ | :------: | :--------: | :-----: | :-----------: |
| resolve soundness        | ✅ sound |  ✅ sound  |  ✗ `¬`  |     ✗ `¬`     |
| resolve completeness     |    ✅    |     ✅     |   ✅    |      ✅       |
| close soundness          |    ✅    |     ✅     |   ✅    |      ✅       |
| close completeness       |    ✅    |     ✅     |   ✅    |      ✅       |
| no double satisfaction   | ✅ holds |   ✗ `¬`    |  ✗ `¬`  |   ✅ holds    |
| mint / burn (compl.+snd) |    ✅    |     ✅     |   n/a   |      n/a      |

`✗ `¬``means the positive property is false and the **negation** is proved
(e.g. the minimal validators let the resolver pay the asset to an arbitrary
address; the vulnerable/minimal validators admit double satisfaction).

## Build

```sh
lake build                              # type-check every proof
lake build Properties.Complete          # one validator module
```
