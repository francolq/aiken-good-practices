# Properties

Lean 4 proofs about the compiled UPLC of `validators/order.ak`.

## Layout

- `Properties/Basic.lean`. Aggregator; importing it pulls every proof.
- `Properties/Common.lean`. Shared `accepts` / `rejects` predicates over
  CEK execution states.
- `Properties/Order/`:
  - `Spec.lean`. Pure-Lean specification of the intended logic. No UPLC.
  - `Completeness.lean`. Loads `order_spend.flat`, builds spend contexts,
    proves `Resolve` / `Close` completeness via `blaster`.
  - `MintCompleteness.lean`. Same for `order_mint.flat` (`Mint` / `Burn`).
  - `Soundness.lean`. `accepts ⇒ spec` for all four branches.
  - `Robustness.lean`. Rejection theorems, including
    `no_double_satisfaction`.
- `Scripts/<name>_<purpose>.flat`. UPLC produced by `aiken uplc encode
--hex` (gitignored, regenerate with `make flats`).

## Build

```sh
lake build                                        # type-check every proof
lake env lean Properties/Order/Completeness.lean  # one module
```

The toolchain is pinned in `lean-toolchain`; `elan` fetches it on first build.
