"""Cache handling and complete snapshot construction for the source audit."""

from __future__ import annotations

import argparse
import copy
from datetime import datetime, timedelta, timezone
import json
import os
from pathlib import Path
import tempfile
from typing import Any

from .lookups import HostRateLimiter, evaluate_source
from .comparisons import (
    classify,
    metadata_comparisons,
    unavailable_comparisons,
)
from .schema import (
    SCHEMA_VERSION,
    catalogue_fingerprint,
    input_fingerprint,
    source_arxiv_id,
    source_catalogue,
    utc_now,
)


ROOT = Path(__file__).resolve().parents[2]
REGISTRY = ROOT / "registry.yaml"
REVIEW = ROOT / "docs/provenance/source-review.json"


def load_cached_records(path: Path = REVIEW) -> dict[str, dict[str, Any]]:
    try:
        snapshot = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if snapshot.get("schema_version") != SCHEMA_VERSION:
        return {}
    records = snapshot.get("records")
    if not isinstance(records, dict):
        return {}
    return {
        source_id: {**record, "related_dois": record.get("related_dois", [])}
        for source_id, record in records.items()
        if isinstance(record, dict)
    }


def cached_record_is_fresh(record: dict[str, Any], max_age_days: float) -> bool:
    checked_on = record.get("checked_on")
    if not isinstance(checked_on, str):
        return False
    try:
        checked_at = datetime.fromisoformat(checked_on.replace("Z", "+00:00"))
    except ValueError:
        return False
    if checked_at.tzinfo is None:
        return False
    return datetime.now(timezone.utc) - checked_at <= timedelta(days=max_age_days)


def cached_record_is_compatible(source: dict[str, Any], record: dict[str, Any]) -> bool:
    """Invalidate legacy HTML-only arXiv rows after the dedicated lookup was added."""
    if not source_arxiv_id(source):
        return isinstance(record.get("related_dois"), list)
    provider = record.get("provider")
    notes = record.get("notes")
    provider_is_current = provider == "arxiv" or (
        provider == "html"
        and isinstance(notes, str)
        and notes.startswith("arXiv API")
    )
    return isinstance(record.get("related_dois"), list) and provider_is_current


def reclassify_record(source: dict[str, Any], record: dict[str, Any]) -> dict[str, Any]:
    """Apply current comparison rules to saved source values without another request."""
    revised = copy.deepcopy(record)
    if revised["lookup_status"] == "OK":
        source_values = {
            comparison["field"]: ""
            if comparison["source_value"] == "—"
            else comparison["source_value"]
            for comparison in revised["metadata"]
        }
        authors = source_values["authors"].split("; ") if source_values["authors"] else []
        external = {
            "identifier": source_values["identifier"],
            "title": source_values["title"],
            "authors": authors,
            "date": source_values["date"],
            "venue": source_values["venue"],
            "volume_issue": source_values["volume_issue"],
            "pages": source_values["pages"],
            "rights": revised["rights"],
            "related_dois": revised.get("related_dois", []),
        }
        comparison_locator = (
            source.get("locator", "")
            if revised["provider"] in {"crossref", "arxiv"}
            else revised["checked_url"]
        )
        revised["metadata"] = metadata_comparisons(
            source, external, True, comparison_locator
        )
    else:
        revised["metadata"] = unavailable_comparisons(source, "UNAVAILABLE")
    revised["status"] = classify(
        revised["lookup_status"],
        revised["metadata"],
        revised["rights"],
        revised.get("related_dois", []),
    )
    return revised


def build_snapshot(args: argparse.Namespace) -> dict[str, Any]:
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    sources = source_catalogue(registry)
    cached = load_cached_records()
    limiter = HostRateLimiter(args.crossref_delay, args.arxiv_delay, args.web_delay)
    records: dict[str, Any] = {}
    total = len(sources)
    if args.reclassify:
        missing = [
            source_id
            for source_id, source in sources.items()
            if not isinstance(cached.get(source_id), dict)
            or cached[source_id].get("input_fingerprint") != input_fingerprint(source)
            or not cached_record_is_compatible(source, cached[source_id])
        ]
        if missing:
            raise ValueError(
                "cannot reclassify without a matching cached record for "
                + ", ".join(sorted(missing))
            )
        for index, (source_id, source) in enumerate(sorted(sources.items()), start=1):
            print(f"[{index}/{total}] {source_id}: reclassifying")
            records[source_id] = reclassify_record(source, cached[source_id])
        return {
            "schema_version": SCHEMA_VERSION,
            "generated_at": utc_now(),
            "source_fingerprint": catalogue_fingerprint(sources),
            "records": records,
        }
    target_sources = (
        set(s.strip() for s in args.sources.split(",") if s.strip())
        if getattr(args, "sources", None)
        else None
    )
    if target_sources is not None:
        unknown = target_sources - set(sources.keys())
        if unknown:
            raise ValueError(
                f"unknown source ID(s) passed to --sources: {', '.join(sorted(unknown))}"
            )
        stale_non_targets = [
            source_id
            for source_id, source in sources.items()
            if source_id not in target_sources
            and (
                not isinstance(cached.get(source_id), dict)
                or cached[source_id].get("input_fingerprint") != input_fingerprint(source)
                or not cached_record_is_compatible(source, cached[source_id])
            )
        ]
        if stale_non_targets:
            raise ValueError(
                "cannot selectively refresh; non-target cached records are missing or stale for current registry: "
                f"{', '.join(sorted(stale_non_targets))}. Run a full refresh or include them in --sources."
            )
    for index, (source_id, source) in enumerate(sorted(sources.items()), start=1):
        cached_record = cached.get(source_id)
        is_target = target_sources is None or source_id in target_sources
        if not is_target and isinstance(cached_record, dict):
            records[source_id] = cached_record
            continue
        if (
            not args.force
            and isinstance(cached_record, dict)
            and cached_record.get("input_fingerprint") == input_fingerprint(source)
            and cached_record_is_fresh(cached_record, args.max_age_days)
            and cached_record_is_compatible(source, cached_record)
        ):
            records[source_id] = cached_record
            print(f"[{index}/{total}] {source_id}: cached")
            continue
        print(f"[{index}/{total}] {source_id}: checking", flush=True)
        records[source_id] = evaluate_source(source, args, limiter)
    return {
        "schema_version": SCHEMA_VERSION,
        "generated_at": utc_now(),
        "source_fingerprint": catalogue_fingerprint(sources),
        "records": records,
    }


def write_snapshot(snapshot: dict[str, Any], path: Path = REVIEW) -> None:
    target = Path(path)
    payload = json.dumps(snapshot, indent=2, ensure_ascii=False) + "\n"
    parent = target.parent
    parent.mkdir(parents=True, exist_ok=True)
    temp_file = tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        dir=parent,
        prefix=f".{target.name}.",
        suffix=".tmp",
        delete=False,
    )
    temp_path = Path(temp_file.name)
    try:
        temp_file.write(payload)
        temp_file.flush()
        temp_file.close()
        os.replace(temp_path, target)
    except BaseException:
        try:
            if not temp_file.closed:
                temp_file.close()
        finally:
            temp_path.unlink(missing_ok=True)
        raise
