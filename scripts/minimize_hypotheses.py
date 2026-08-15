#!/usr/bin/env python3
"""Find hypotheses a theorem does not need.

`#print axioms` reports the weakest *axioms* a proof rests on and `#min_imports`
the weakest *imports*. Neither answers the third question a reverse-proving loop
asks: which stated hypotheses is the theorem actually true without?

Lean's unused-variable linter catches a binder the proof never mentions. It does
not catch a binder the proof *uses* while the statement holds without it — the
proof simply took a convenient route. That gap is where unused side conditions
accumulate, and it is about to get worse: restating section 8 over
`MeasurableSpace` adds a measurability hypothesis to every signature.

The test is mechanical. Delete a hypothesis binder, elaborate the file, and see
what happens:

* the file still compiles  -> `REMOVABLE`, the hypothesis is not needed;
* the theorem itself fails -> `USED`, the proof needs it;
* a later declaration fails -> `CALLSITE`, removable here but callers pass it.

This is an offline audit, not a gate: each candidate costs a full elaboration of
the module. Run it on one declaration at a time.

    python3 scripts/minimize_hypotheses.py AISafetyAtlas/Inference/Foo.lean --decl bar

Binders are recognised by the atlas's own naming convention -- explicit
parenthesised binders whose name begins with `h` or `_h`. Implicit `{}` and
instance `[]` binders are never touched, since removing them breaks elaboration
for reasons that say nothing about necessity.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Lean identifiers here include subscripts and primes, which the atlas uses freely.
TAIL = r"[A-Za-z0-9_'′₀-₉¹²³]*"
NAME = rf"[A-Za-z_]{TAIL}"
DECL_RE = re.compile(rf"^\s*(?:@\[[^\]]*\]\s*)?(?:public\s+|private\s+)?theorem\s+({NAME})")
BINDER_RE = re.compile(rf"\((_?h{TAIL})\s*:")


def declaration_spans(text: str) -> list[tuple[str, int, int]]:
    """Return `(name, start_line, end_line)` for every theorem, 0-indexed."""
    lines = text.splitlines()
    starts: list[tuple[str, int]] = []
    for i, line in enumerate(lines):
        found = DECL_RE.match(line)
        if found:
            starts.append((found.group(1), i))
    spans: list[tuple[str, int, int]] = []
    for k, (name, start) in enumerate(starts):
        end = starts[k + 1][1] - 1 if k + 1 < len(starts) else len(lines) - 1
        spans.append((name, start, end))
    return spans


def signature_end(text: str, start_offset: int) -> int:
    """Offset of the `:=` or `by` that ends a declaration's signature."""
    depth = 0
    i = start_offset
    while i < len(text):
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and text.startswith(":=", i):
            return i
        i += 1
    return len(text)


def binder_spans(text: str, decl_start: int, decl_end: int) -> list[tuple[str, int, int]]:
    """Explicit hypothesis binders inside one declaration's signature."""
    sig_end = signature_end(text, decl_start)
    limit = min(sig_end, decl_end)
    out: list[tuple[str, int, int]] = []
    for m in BINDER_RE.finditer(text, decl_start, limit):
        open_at = m.start()
        depth = 0
        j = open_at
        while j < len(text):
            if text[j] == "(":
                depth += 1
            elif text[j] == ")":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        if j < len(text):
            out.append((m.group(1), open_at, j + 1))
    return out


HAVE_RE = re.compile(rf"\bhave\s+(_{TAIL})\s*[:∀({{\[]")


def dead_haves(text: str, spans: list[tuple[str, int, int]]) -> list[tuple[str, str]]:
    """`have _x := …` whose result is never used again in the same proof.

    A hypothesis consumed only by such a step is reported `USED` by the deletion
    test while the theorem is true without it: the proof mentions it, but only to
    build something it then discards. Reporting these separately turns a
    misleading `USED` into an actionable one.
    """
    lines = text.splitlines()
    out: list[tuple[str, str]] = []
    for name, start, end in spans:
        body = lines[start : end + 1]
        for i, line in enumerate(body):
            m = HAVE_RE.search(line)
            if not m:
                continue
            bound = m.group(1)
            rest = "\n".join(body[i + 1 :])
            if not re.search(rf"(?<![A-Za-z0-9_']){re.escape(bound)}(?![A-Za-z0-9_'])", rest):
                out.append((name, bound))
    return out


def elaborate(path: Path, timeout: int) -> tuple[bool, str]:
    proc = subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    return proc.returncode == 0, proc.stdout + proc.stderr


def first_error_line(output: str, fallback: int) -> int:
    """1-indexed source line of the first reported error."""
    m = re.search(r"\.lean:(\d+):\d+: error", output)
    return int(m.group(1)) if m else fallback


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("module", help="path to a .lean file under the repository root")
    ap.add_argument("--decl", help="only audit this declaration")
    ap.add_argument("--timeout", type=int, default=900, help="seconds per candidate")
    ap.add_argument(
        "--dead-haves-only",
        action="store_true",
        help="run only the cheap syntactic scan, no elaboration",
    )
    args = ap.parse_args()

    source = ROOT / args.module
    if not source.is_file():
        print(f"no such file: {source}", file=sys.stderr)
        return 2
    text = source.read_text(encoding="utf-8")

    spans = declaration_spans(text)
    if args.decl:
        spans = [s for s in spans if s[0] == args.decl]
        if not spans:
            print(f"no theorem named {args.decl} in {args.module}", file=sys.stderr)
            return 2

    for decl, bound in dead_haves(text, spans):
        print(f"{'DEAD-HAVE':<10} {decl}  (have {bound} … never used again)")
    if args.dead_haves_only:
        return 0

    line_offsets = [0]
    for line in text.splitlines(keepends=True):
        line_offsets.append(line_offsets[-1] + len(line))

    findings: list[tuple[str, str, str]] = []
    for name, start_line, end_line in spans:
        decl_start = line_offsets[start_line]
        decl_end = line_offsets[min(end_line + 1, len(line_offsets) - 1)]
        binders = binder_spans(text, decl_start, decl_end)
        for binder, lo, hi in binders:
            candidate = text[:lo].rstrip(" ") + text[hi:]
            with tempfile.NamedTemporaryFile(
                "w", suffix=".lean", dir=source.parent, delete=False, encoding="utf-8"
            ) as tmp:
                tmp.write(candidate)
                tmp_path = Path(tmp.name)
            try:
                ok, output = elaborate(tmp_path, args.timeout)
            except subprocess.TimeoutExpired:
                ok, output = False, "timeout"
            finally:
                tmp_path.unlink(missing_ok=True)

            if ok:
                verdict = "REMOVABLE"
            elif output == "timeout":
                verdict = "TIMEOUT"
            else:
                err_line = first_error_line(output, start_line + 1)
                inside = start_line + 1 <= err_line <= end_line + 1
                verdict = "USED" if inside else "CALLSITE"
            findings.append((name, binder, verdict))
            print(f"{verdict:<10} {name}  ({binder} : …)", flush=True)

    removable = [f for f in findings if f[2] == "REMOVABLE"]
    callsite = [f for f in findings if f[2] == "CALLSITE"]
    print(
        f"\nminimize_hypotheses: {len(findings)} candidates, "
        f"{len(removable)} REMOVABLE, {len(callsite)} CALLSITE"
    )
    if removable:
        print("A REMOVABLE hypothesis is stated but not needed. Either drop it, or "
              "record in the declaration's docstring why print fidelity keeps it.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
