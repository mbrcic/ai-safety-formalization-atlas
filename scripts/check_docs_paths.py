#!/usr/bin/env python3
"""Smoke-check that markdown links to repo-relative paths resolve.

Scans selected docs for markdown links of the form [text](path) where path is
relative (not http/https/mailto/#). Exits non-zero if any target is missing.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LINK = re.compile(r"\]\(([^)]+)\)")

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
    if missing:
        print(f"docs path check: {len(missing)} missing of {checked} relative links", file=sys.stderr)
        for line in missing[:50]:
            print(f"  {line}", file=sys.stderr)
        if len(missing) > 50:
            print(f"  … and {len(missing) - 50} more", file=sys.stderr)
        raise SystemExit(1)
    print(f"docs path check ok: {checked} relative links in {len(candidates())} files")


if __name__ == "__main__":
    main()
