#!/usr/bin/env python3
"""Smoke-check that references to repo-relative paths resolve.

Two passes. Markdown links of the form [text](path) in the docs tree, and bare
`docs/...` paths written into ledger prose — registry notes, task bodies,
conjecture rationales. The second pass exists because a note in registry.yaml
pointed at `docs/status/paper-coverage.md` for weeks after that file was
deleted: the ledger is prose too, and nothing was reading it.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LINK = re.compile(r"\]\(([^)]+)\)")

# A bare repository path mentioned in ledger prose. Deliberately narrow: only
# `docs/...` ending in a file extension, so ordinary sentences are not mistaken
# for links.
LEDGER_PATH = re.compile(r"\bdocs/[A-Za-z0-9_./-]+\.[A-Za-z0-9]{1,5}\b")
LEDGERS = ["registry.yaml", "tasks.yaml", "conjectures.yaml"]

SCAN_GLOBS = [
    "README.md",
    "ROADMAP.md",
    "STATE.md",
    "AGENTS.md",
    "CONTRIBUTING.md",
    "docs/**/*.md",
]


def candidates() -> list[Path]:
    files: list[Path] = []
    for pattern in SCAN_GLOBS:
        files.extend(ROOT.glob(pattern))
    return sorted({p.resolve() for p in files if p.is_file()})


def ledger_strings(value: object) -> list[str]:
    """Every string anywhere in a decoded ledger, at any nesting depth."""
    if isinstance(value, str):
        return [value]
    if isinstance(value, dict):
        return [s for v in value.values() for s in ledger_strings(v)]
    if isinstance(value, list):
        return [s for v in value for s in ledger_strings(v)]
    return []


def check_ledger_prose() -> tuple[int, list[str]]:
    """Resolve bare `docs/...` paths written into ledger text fields."""
    missing: list[str] = []
    checked = 0
    for name in LEDGERS:
        path = ROOT / name
        if not path.is_file():
            continue
        for text in ledger_strings(json.loads(path.read_text(encoding="utf-8"))):
            for target in set(LEDGER_PATH.findall(text)):
                checked += 1
                if not (ROOT / target).exists():
                    missing.append(f"{name} -> {target}")
    return checked, sorted(set(missing))


def main() -> None:
    missing: list[str] = []
    checked = 0
    for path in candidates():
        text = path.read_text(encoding="utf-8")
        for match in LINK.finditer(text):
            raw = match.group(1).strip()
            if not raw or raw.startswith(("#", "http://", "https://", "mailto:")):
                continue
            # strip optional title 'path "title"'
            target = raw.split()[0].strip("<>")
            if target.startswith(("http://", "https://", "mailto:")):
                continue
            # anchors only
            if target.startswith("#"):
                continue
            file_part, _, _anchor = target.partition("#")
            if not file_part:
                continue
            resolved = (path.parent / file_part).resolve()
            checked += 1
            if not resolved.exists():
                try:
                    rel = resolved.relative_to(ROOT)
                except ValueError:
                    rel = resolved
                missing.append(f"{path.relative_to(ROOT)} -> {file_part} (resolved {rel})")
    ledger_checked, ledger_missing = check_ledger_prose()
    checked += ledger_checked
    missing.extend(ledger_missing)
    if missing:
        print(f"docs path check: {len(missing)} missing of {checked} relative links", file=sys.stderr)
        for line in missing[:50]:
            print(f"  {line}", file=sys.stderr)
        if len(missing) > 50:
            print(f"  … and {len(missing) - 50} more", file=sys.stderr)
        raise SystemExit(1)
    print(
        f"docs path check ok: {checked} relative links in "
        f"{len(candidates())} docs and {len(LEDGERS)} ledgers"
    )


if __name__ == "__main__":
    main()
