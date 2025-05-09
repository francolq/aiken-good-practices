# order-book

Code for TxPipe Crew Show&Tell.

## Workflow

Compile with:

```sh
aiken build
```

Compile with traces (for debugging) with:
```sh
aiken build --trace-level verbose
```

Build lucid blueprints with:
```sh
deno run -A https://deno.land/x/lucid/blueprint.ts
```

Test using basic trace:
```sh
deno tests/integration.ts
```

Test for composability:
```sh
deno tests/composition.ts
```
