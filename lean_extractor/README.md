# `lean_extractor` — Lean 4 Kernel `.olean` DAG Extractor

Self-contained Lean 4 metaprogram that loads a compiled Lean 4 `Environment`, traverses `Expr.getUsedConstants` starting from one or more target theorems (stopping at Mathlib/Init/Std/Lean boundaries by default), and emits newline-delimited JSON (JSONL) directly consumable by `proof_compressor.ingest.olean_bridge.ingest_olean_jsonl`.

## Build

Requires Lean 4 / Lake matching `lean-toolchain` (`leanprover/lean4:v4.34.1`):

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd lean_extractor
lake build
```

## Self-Test

Extract the built-in `ExtractDag.demoTheorem` DAG from `ExtractDag.olean`:

```bash
lake env .lake/build/bin/extract_dag --self-test --out /tmp/demo_dag.jsonl
```

Then ingest into SQLite with `proof-compressor`:

```bash
proof-compressor ingest-olean /tmp/demo_dag.jsonl --db /tmp/demo.db
```

## Running Against a Compiled Lean 4 Project

From the target Lean 4 project directory (after `lake build` has produced `.olean` files):

```bash
lake env /path/to/proof-compressor/lean_extractor/.lake/build/bin/extract_dag \
  --module Main \
  --root riemannHypothesis \
  --root LFunction_eq_zero_re \
  --out rh_kernel_dag.jsonl
```

## JSONL Output Schema

Each line is a JSON object with:

- `name`: Fully qualified Lean constant name
- `module`: Dotted Lean module path
- `kind`: `theorem`, `def`, `axiom`, `inductive`, `opaque`, `quot`, `ctor`, `rec`
- `type`: Pretty-printed type signature (`Meta.ppExpr`)
- `proof_term_size`: Unique kernel `Expr` DAG node count
- `is_mathlib`: Boolean indicating Mathlib/Init/Std/Lean/Batteries boundary
- `axioms`: Array of kernel axiom names (`Lean.CollectAxioms.collect`)
- `type_deps`: Array of constants appearing in the type expression
- `value_deps`: Array of constants appearing in the value/proof expression
- `docstring`: Optional Lean docstring if present
