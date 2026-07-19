#!/usr/bin/env python3
"""Rebuild formal-library discovery evidence from pinned local source trees."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import unicodedata


ROOT = Path(__file__).resolve().parents[1]
REGISTRY_PATH = ROOT / "registry.yaml"
EVIDENCE_PATH = ROOT / "docs/provenance/formalization-search.json"
SUMMARY_PATH = ROOT / "docs/provenance/formalization-search.md"
MAX_RECORDED_PATHS = 12
SOURCE_SUFFIXES = {
    ".agda",
    ".lean",
    ".lagda",
    ".md",
    ".ml",
    ".mli",
    ".rst",
    ".sig",
    ".sml",
    ".tex",
    ".thy",
    ".txt",
    ".v",
}


def parse_mapping(values: list[str], option: str) -> dict[str, Path]:
    mappings: dict[str, Path] = {}
    for value in values:
        if "=" not in value:
            raise SystemExit(f"{option} expects CORPUS=PATH, got {value!r}")
        name, raw_path = value.split("=", 1)
        mappings[name] = Path(raw_path).resolve()
    return mappings


def normalized(text: str) -> str:
    decomposed = unicodedata.normalize("NFKD", text).casefold()
    without_marks = "".join(
        char for char in decomposed if unicodedata.category(char) != "Mn"
    )
    return " ".join(re.sub(r"[^a-z0-9]+", " ", without_marks).split())


def git_root(path: Path) -> Path | None:
    for candidate in (path, *path.parents):
        if (candidate / ".git").exists():
            return candidate
    return None


def verify_corpus(name: str, path: Path, metadata: dict[str, object]) -> None:
    if not path.is_dir():
        raise SystemExit(f"corpus root does not exist: {name}={path}")
    version = str(metadata["version"])
    if re.fullmatch(r"[0-9a-f]{40}", version):
        repository = git_root(path)
        if repository is None:
            raise SystemExit(f"{name} must be inside a Git checkout at {version}")
        actual = subprocess.run(
            ["git", "-C", str(repository), "rev-parse", "HEAD"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        if actual != version:
            raise SystemExit(f"{name} revision mismatch: expected {version}, got {actual}")
    elif name == "isabelle-afp" and "2026-02-06" not in path.name:
        raise SystemExit(
            "isabelle-afp root must be the extracted afp-2026-02-06 directory"
        )


def source_files(root: Path) -> list[Path]:
    return sorted(
        path
        for path in root.rglob("*")
        if path.is_file()
        and ".git" not in path.parts
        and path.suffix.casefold() in SOURCE_SUFFIXES
        and path.stat().st_size <= 8 * 1024 * 1024
    )


def displayed_path(corpus: str, root: Path, path: Path) -> str:
    relative = path.relative_to(root).as_posix()
    if corpus == "isabelle-afp":
        return f"{root.name}/{relative}"
    return relative


def search_corpus(
    corpus: str,
    root: Path,
    queries_by_result: dict[str, list[str]],
) -> dict[str, dict[str, object]]:
    normalized_queries = {
        result_id: {query: normalized(query) for query in queries}
        for result_id, queries in queries_by_result.items()
    }
    matches = {
        result_id: {query: set() for query in queries}
        for result_id, queries in queries_by_result.items()
    }

    for path in source_files(root):
        try:
            content = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        haystack = normalized(f"{path.relative_to(root).as_posix()}\n{content}")
        padded_haystack = f" {haystack} "
        shown_path = displayed_path(corpus, root, path)
        for result_id, query_map in normalized_queries.items():
            for query, needle in query_map.items():
                if needle and f" {needle} " in padded_haystack:
                    matches[result_id][query].add(shown_path)

    evidence: dict[str, dict[str, object]] = {}
    for result_id, query_matches in matches.items():
        all_paths = sorted(set().union(*query_matches.values()))
        counts = {query: len(paths) for query, paths in query_matches.items()}
        evidence[result_id] = {
            "hit_count": len(all_paths),
            "query_hit_counts": counts,
            "paths": all_paths[:MAX_RECORDED_PATHS],
            "matched_queries": [query for query, count in counts.items() if count],
        }
    return evidence


def render_summary(registry: dict[str, object], evidence: dict[str, object]) -> str:
    lines = [
        "# Formal-Library Search Evidence",
        "",
        f"Search date: {evidence['searched_on']}",
        "",
        "This is a version-pinned, scoped discovery pass across maintained corpora.",
        "A candidate hit is not a verified formalization, and zero keyword hits do",
        "not prove nonexistence. Counts are unions of files matching at least one",
        "query; query-level counts and up to 12 representative paths per corpus are",
        "recorded in `formalization-search.json`. High raw counts usually indicate",
        "broad query noise rather than coverage. Only statement-level checked matches",
        "belong in `registry.yaml` under `formalizations`.",
        "",
        "## Corpora",
        "",
        "| ID | Framework | Version | Scope |",
        "|---|---|---|---|",
    ]
    for corpus_id, corpus in evidence["corpora"].items():
        lines.append(
            f"| {corpus_id} | {corpus['framework']} | `{corpus['version']}` | "
            f"{corpus['scope']} |"
        )
    lines.extend(
        [
            "",
            "## Per-result discovery",
            "",
            "| ID | Result | Query terms | Candidate corpora | Raw candidate files |",
            "|---|---|---|---|---:|",
        ]
    )
    evidence_results = evidence["results"]
    for result in registry["results"]:
        result_evidence = evidence_results[result["id"]]
        queries = ", ".join(f"`{query}`" for query in result_evidence["queries"])
        candidate_corpora = [
            corpus
            for corpus, hit in result_evidence["candidate_hits"].items()
            if hit["hit_count"]
        ]
        corpora_text = ", ".join(candidate_corpora) if candidate_corpora else "none"
        hit_count = sum(
            hit["hit_count"] for hit in result_evidence["candidate_hits"].values()
        )
        lines.append(
            f"| {result['id']} | {result['name']} | {queries} | {corpora_text} | "
            f"{hit_count} |"
        )
    lines.extend(
        [
            "",
            "Full candidate paths and per-query counts are in "
            "[`formalization-search.json`](formalization-search.json). Review "
            "candidates against source statements before changing a registry "
            "relationship or status.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--corpus-root",
        action="append",
        default=[],
        metavar="CORPUS=PATH",
        help="local checkout or extracted source root; repeat for every corpus",
    )
    parser.add_argument(
        "--result",
        action="append",
        default=[],
        help="result ID to rebuild; omit to rebuild every result",
    )
    parser.add_argument("--write", action="store_true", help="write updated evidence")
    args = parser.parse_args()

    registry = json.loads(REGISTRY_PATH.read_text(encoding="utf-8"))
    evidence = json.loads(EVIDENCE_PATH.read_text(encoding="utf-8"))
    corpus_roots = parse_mapping(args.corpus_root, "--corpus-root")
    expected_corpora = list(evidence["corpora"])
    missing = [corpus for corpus in expected_corpora if corpus not in corpus_roots]
    if missing:
        raise SystemExit(f"missing --corpus-root entries: {', '.join(missing)}")
    for corpus in expected_corpora:
        verify_corpus(corpus, corpus_roots[corpus], evidence["corpora"][corpus])

    registry_results = {result["id"]: result for result in registry["results"]}
    selected = args.result or list(registry_results)
    unknown = [result_id for result_id in selected if result_id not in registry_results]
    if unknown:
        raise SystemExit(f"unknown result IDs: {', '.join(unknown)}")
    queries_by_result = {
        result_id: registry_results[result_id]["formal_library_search"]["query_terms"]
        for result_id in selected
    }

    corpus_evidence = {
        corpus: search_corpus(corpus, corpus_roots[corpus], queries_by_result)
        for corpus in expected_corpora
    }
    for result_id in selected:
        queries = queries_by_result[result_id]
        candidate_hits = {
            corpus: corpus_evidence[corpus][result_id] for corpus in expected_corpora
        }
        evidence["results"][result_id] = {
            "queries": queries,
            "candidate_hits": candidate_hits,
        }
        candidate_corpora = [
            corpus for corpus, hit in candidate_hits.items() if hit["hit_count"]
        ]
        search_record = registry_results[result_id]["formal_library_search"]
        search_record["query_terms"] = queries
        search_record["candidate_corpora"] = candidate_corpora

    evidence["schema_version"] = 2
    evidence["method"] = (
        "Case-insensitive Unicode-normalized token and phrase search over pinned source "
        "snapshots. Hits are candidates, not verified formalizations; per-query "
        "counts expose noisy terms, and zero hits are scoped negative evidence only."
    )

    for result_id in selected:
        total = sum(
            hit["hit_count"]
            for hit in evidence["results"][result_id]["candidate_hits"].values()
        )
        print(f"{result_id}: {total} candidate files")

    if args.write:
        REGISTRY_PATH.write_text(
            json.dumps(registry, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
        EVIDENCE_PATH.write_text(
            json.dumps(evidence, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
        SUMMARY_PATH.write_text(render_summary(registry, evidence), encoding="utf-8")


if __name__ == "__main__":
    main()
