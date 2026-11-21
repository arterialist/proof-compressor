# proof-compressor

A high-throughput toolkit for compressing, analyzing, and exposing massive Lean 4 proof repositories (such as multi-million-line formalizations) into structured dependency databases, human-readable Annals-style LaTeX manuscripts, interactive zoomable proof blueprints, and kernel-checked refactoring plans.

## Architecture

1. **Streaming Ingestion (`proof_compressor.ingest` & `lean_extractor/`)**
   - Streams `.lean` sources directly from single or multi-part `.tar.gz` archives (zero disk extraction) or Lean 4 `.olean` kernel exports into a compact SQLite database.
2. **Graph & Topology Analysis (`proof_compressor.analyze`)**
   - Exact reverse-dependency reachability pruning from root theorems.
   - Canonical type-hash deduplication and Mathlib-absorption detection.
   - Scalable iterative Tarjan SCC, Cooper–Harvey–Kennedy dominator trees, bottleneck scoring, and hierarchical modular DAG clustering.
3. **Mathematical Exposition & Auditing (`proof_compressor.expose`)**
   - Symbol registry mapping Lean declarations to standard mathematical notation.
   - Bookkeeping/glue filtering and proof-idiom tagging.
   - Deterministic Annals-style `paper.tex` synthesis, interactive three-level `blueprint.html`, and automated graph-fidelity auditing (`audit_report.json`).
4. **Kernel-Checked Refactoring (`proof_compressor.refactor`)**
   - Identifies high-leverage refactoring targets (`Inputs ⊢ Outputs`) and verifies replacements via `lake build`, `#print axioms`, and strict LOC reduction checks.

## Quickstart

```bash
uv sync
uv run proof-compressor --help
uv run pytest
```
