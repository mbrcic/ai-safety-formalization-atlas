#!/usr/bin/env python3
"""Refresh the complete, cacheable source metadata and rights audit.

The command-line surface stays small. Catalogue parsing, public lookups, and
snapshot handling live in ``scripts/source_review/`` so each part can be read
and tested independently.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from source_review.snapshot import build_snapshot, write_snapshot


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Refresh the complete public-source metadata and rights audit."
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="re-query selected sources, or all works when --sources is omitted",
    )
    parser.add_argument(
        "--sources",
        help="comma-separated list of source IDs to re-query, reusing cache for all others",
    )
    parser.add_argument(
        "--reclassify",
        action="store_true",
        help="reapply comparison rules to saved evidence without a network request",
    )
    parser.add_argument(
        "--mailto",
        help="optional address supplied only to Crossref's polite pool; never stored",
    )
    parser.add_argument("--crossref-delay", type=float, default=1.0)
    parser.add_argument("--arxiv-delay", type=float, default=3.0)
    parser.add_argument("--web-delay", type=float, default=1.0)
    parser.add_argument(
        "--max-age-days",
        type=float,
        default=30.0,
        help="reuse a matching cached result only while it is this many days old",
    )
    parser.add_argument("--timeout", type=float, default=20.0)
    parser.add_argument("--max-bytes", type=int, default=1_000_000)
    parser.add_argument("--retries", type=int, default=2)
    parser.add_argument(
        "--user-agent",
        default=(
            "AI-Safety-Formalization-Atlas source-review/1.0 "
            "(+https://github.com/mbrcic/ai-safety-formalization-atlas)"
        ),
    )
    args = parser.parse_args()
    if args.force and args.reclassify:
        parser.error("--force and --reclassify cannot be used together")
    if args.sources and args.reclassify:
        parser.error("--sources and --reclassify cannot be used together")
    if min(args.crossref_delay, args.arxiv_delay, args.web_delay, args.max_age_days) < 0:
        parser.error("delays and max-age-days must be non-negative")
    if args.timeout <= 0 or args.max_bytes <= 0 or args.retries < 0:
        parser.error("timeout and max-bytes must be positive; retries must be non-negative")
    return args


def main() -> None:
    snapshot = build_snapshot(parse_args())
    write_snapshot(snapshot)
    counts: dict[str, int] = {}
    for record in snapshot["records"].values():
        status = record["status"]
        counts[status] = counts.get(status, 0) + 1
    print(
        "source review refreshed: "
        + ", ".join(f"{status}={count}" for status, count in sorted(counts.items()))
    )


if __name__ == "__main__":
    main()
