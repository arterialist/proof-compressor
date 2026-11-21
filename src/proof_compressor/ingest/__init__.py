"""Lean 4 source and .olean kernel ingestion pipelines."""

from proof_compressor.ingest.lean_parser import (
    ParsedDecl,
    ParsedModule,
    canonical_type_hash,
    canonicalize_type,
    extract_identifiers,
    is_bookkeeping_decl,
    normalize_module_path,
    parse_lean_source,
)
from proof_compressor.ingest.olean_bridge import (
    OleanIngestStats,
    ingest_olean_jsonl,
)
from proof_compressor.ingest.stream_archive import (
    IngestStats,
    ingest_source,
    iter_lean_sources,
    resolve_input_source,
)

__all__ = [
    "IngestStats",
    "OleanIngestStats",
    "ParsedDecl",
    "ParsedModule",
    "canonical_type_hash",
    "canonicalize_type",
    "extract_identifiers",
    "ingest_olean_jsonl",
    "ingest_source",
    "is_bookkeeping_decl",
    "iter_lean_sources",
    "normalize_module_path",
    "parse_lean_source",
    "resolve_input_source",
]
