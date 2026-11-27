#!/usr/bin/env python3
"""Check the printed-statement transcriptions in docs/provenance/printed-statements/.

Each YAML file there holds a source's printed statements, the definitions they
use and the source's standing assumptions, transcribed in LaTeX from the page
image (README.md in that folder). This checks what can be checked without the
page images:

* every file parses and has the fields README.md requires;
* the source hash is a sha256 and, when the pinned PDF is present locally
  (``--literature DIR``), matches the file;
* ids are unique within a file, and every ``uses``/``for`` reference resolves, in
  the same file or as ``<file-stem>#<id>`` in another one;
* with ``--rows KEY.json``, every graded audit row appears exactly once.

``--require-checked`` additionally fails on any entry without a second reader
(``checked``); grading must not use a file before that passes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
DIR = ROOT / "docs/provenance/printed-statements"
SHA = re.compile(r"^[0-9a-f]{64}$")
ENTRY_FIELDS = {
    "definitions": ("id", "label", "pdf_page", "latex", "transcribed"),
    "statements": ("id", "audit_row", "locator", "pdf_page", "label", "latex", "transcribed"),
    "excerpts": ("id", "for", "reason", "pdf_page", "latex", "transcribed"),
}


def load(dir_: Path) -> dict[str, dict]:
    return {p.stem: yaml.safe_load(p.read_text(encoding="utf-8")) for p in sorted(dir_.glob("*.yaml"))}


def check(files: dict[str, dict], literature: Path | None, rows: set[str] | None,
          require_checked: bool) -> list[str]:
    errs: list[str] = []
    ids = {stem: {e["id"] for k in ENTRY_FIELDS for e in (d.get(k) or []) if isinstance(e, dict) and "id" in e}
           for stem, d in files.items()}
    seen_rows: dict[str, str] = {}
    for stem, d in files.items():
        src = d.get("source") or {}
        for f in ("citation", "file", "sha256"):
            if not src.get(f):
                errs.append(f"{stem}: source.{f} missing")
        sha = str(src.get("sha256", ""))
        if not SHA.match(sha):
            errs.append(f"{stem}: source.sha256 is not a sha256")
        elif literature is not None:
            pdf = literature / str(src.get("file", ""))
            if pdf.exists():
                if hashlib.sha256(pdf.read_bytes()).hexdigest() != sha:
                    errs.append(f"{stem}: sha256 does not match {pdf.name}")
            else:
                errs.append(f"{stem}: {pdf.name} not found in {literature}")
        count: dict[str, int] = {}
        for kind, fields in ENTRY_FIELDS.items():
            for e in d.get(kind) or []:
                where = f"{stem}:{kind}:{e.get('id', '?')}"
                for f in fields:
                    if f not in e:
                        errs.append(f"{where}: missing {f}")
                count[e.get("id")] = count.get(e.get("id"), 0) + 1
                if kind == "statements" and e.get("latex") is None and not e.get("note"):
                    errs.append(f"{where}: latex null without a note saying what was searched")
                if require_checked and not e.get("checked"):
                    errs.append(f"{where}: not second-read (checked missing)")
                for ref in (e.get("uses") or []) + (e.get("for") or []):
                    other, _, rid = ref.rpartition("#")
                    target = other or stem
                    if rid not in ids.get(target, set()):
                        errs.append(f"{where}: reference {ref} does not resolve")
                if kind == "statements" and e.get("audit_row"):
                    r = e["audit_row"]
                    if r in seen_rows:
                        errs.append(f"{where}: audit row {r} also in {seen_rows[r]}")
                    seen_rows[r] = where
        errs += [f"{stem}: id {i} used {n} times" for i, n in count.items() if n > 1]
    if rows is not None:
        missing = sorted(rows - seen_rows.keys())
        extra = sorted(seen_rows.keys() - rows)
        if missing:
            errs.append(f"{len(missing)} graded rows not transcribed: {', '.join(missing[:20])}"
                        + (" ..." if len(missing) > 20 else ""))
        if extra:
            errs.append(f"rows not in the graded set: {', '.join(extra)}")
    return errs


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--dir", type=Path, default=DIR)
    ap.add_argument("--literature", type=Path, help="folder holding the pinned PDFs")
    ap.add_argument("--rows", type=Path, help="regrade KEY.json; require every row once")
    ap.add_argument("--require-checked", action="store_true")
    a = ap.parse_args()
    files = load(a.dir)
    rows = {v["row_id"] for v in json.loads(a.rows.read_text(encoding="utf-8")).values()} if a.rows else None
    errs = check(files, a.literature, rows, a.require_checked)
    n = sum(len(d.get("statements") or []) for d in files.values())
    for e in errs:
        print(e)
    print(f"check_printed_statements: {len(files)} files, {n} statements, {len(errs)} problems")
    return 1 if errs else 0


if __name__ == "__main__":
    sys.exit(main())
