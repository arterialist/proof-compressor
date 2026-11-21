"""proof-compressor: Compress massive formal Lean 4 proofs into human-readable mathematics."""

from proof_compressor.schema import (
    SCHEMA_VERSION,
    connect_db,
    create_indexes,
    finalize_bulk,
    get_all_meta,
    get_db_summary,
    get_meta,
    init_db,
    set_meta,
)

__version__ = "0.1.0"

__all__ = [
    "__version__",
    "SCHEMA_VERSION",
    "connect_db",
    "create_indexes",
    "finalize_bulk",
    "get_all_meta",
    "get_db_summary",
    "get_meta",
    "init_db",
    "set_meta",
]
