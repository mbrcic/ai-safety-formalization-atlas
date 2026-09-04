#!/usr/bin/env python3
"""Notice when a graded statement changes, because nothing else does.

`AGENTS.md` § Statement freeze: once a statement carries a fidelity grade, its
binders, hypotheses, quantifiers and conclusion are frozen; proof bodies are
not. Weakening a hypothesis to make a proof go through is a schema event — the
row has to be re-graded, because a grade earned by the old statement does not
transfer to the new one.

Every gate in this repository is blind to that. The kernel checks the proof, the
axiom audit checks what it rests on, the view generators check that names still
resolve — and all of them stay green when a statement quietly becomes a
different statement. Every fidelity defect this repository has shipped and later
fixed was of exactly that kind, and every one compiled.

So this hashes the *signature* — everything from the declaration keyword up to
the `:=` that starts the proof — of each declaration the registry or conjecture
ledger grades, and compares it against `docs/status/statement-lock.json`. A
difference is not a failure. It is a question: *did fidelity move, and in which
direction?* Answer it in the change that causes it, re-grade the row if the
answer is yes, and run `--write` to record the new statement.

**Deliberately crude.** It compares source text, not elaborated types, so
reformatting a signature or renaming a bound variable reports a change that is
not one. That is the right way to be wrong here: a false positive costs one
question, a false negative is the defect the rule exists to catch. Precision
would need an elaboration pipeline, which costs minutes per run to buy a
smaller improvement than the check itself delivers.

Advisory: exits 0 whatever it finds. Exits 1 only when it cannot answer at all.

Usage:
    python3 scripts/check_statement_freeze.py            # report drift
    python3 scripts/check_statement_freeze.py --write    # record the current statements
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BY_ID = ROOT / "docs" / "agent" / "by-id.json"
CONJECTURES = ROOT / "conjectures.yaml"
DECLARATION_INDEX = ROOT / "docs" / "status" / "declaration-index.json"
LOCK = ROOT / "docs" / "status" / "statement-lock.json"

DECLARATION_KEYWORDS = (
    "theorem", "lemma", "def", "abbrev", "structure", "class", "instance",
    "inductive", "opaque", "axiom",
)
LINE_COMMENT = re.compile(r"--.*$")
BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)


def signature(text: str, line: int) -> str | None:
    """The declaration's statement: from its keyword to the proof's `:=`.

    `line` is 1-based and points at the declaration, per `by-id.json`. The scan
    stops at the first top-level `:=`, at `where`, or at a blank line, so a
    structure's fields and a theorem's proof are both excluded — what remains is
    the thing the fidelity grade was earned by.
    """
    lines = text.split("\n")
    if not 1 <= line <= len(lines):
        return None
    collected: list[str] = []
    for raw in lines[line - 1:line - 1 + 60]:
        stripped = LINE_COMMENT.sub("", raw)
        if ":=" in stripped:
            collected.append(stripped.split(":=")[0])
            break
        if re.match(r"\s*where\b", stripped):
            break
        if collected and not stripped.strip():
            break
        collected.append(stripped)
    else:
        return None
    body = BLOCK_COMMENT.sub(" ", "\n".join(collected))
    return re.sub(r"\s+", " ", body).strip() or None


# Frontier specification surfaces.
#
# Neither source below reaches these. They are not reproduced external
# formalizations, so no registry `lean_artifact` row names them; and a
# conjecture row freezes exactly one declaration, which for CONJ-026 is
# `IsO70RankTable`. Yet they are the statements a silent edit would damage
# most: each is the `P ↔ body` surface of a hypothesis the atlas *assumes and
# does not prove*, and freezing the alias alone freezes nothing, because the
# body sits behind a `def`. Weakening a frontier is the cheapest way to make a
# conditional theorem look stronger than it is, and this is what notices.
#
# Kept as a literal rather than a new ledger field: there are two, they are
# hand-chosen, and a diff to this list is exactly the review event that should
# accompany adding or retiring a frontier.
SPECIFICATION_SURFACES = {
    "AISafetyAtlas.SingularLearning.eigenvalueLawStatement_iff":
        "AISafetyAtlas/SingularLearning/EigenvalueLaw.lean",
    "AISafetyAtlas.Conjectures.MAIS.o70ExactLocalPairsExist_iff":
        "AISafetyAtlas/Conjectures/MAIS/O70.lean",
    "AISafetyAtlas.Conjectures.MAIS.o70ZetaPoleBridge_iff":
        "AISafetyAtlas/Conjectures/MAIS/O70.lean",
}


def declaration_line(text: str, name: str) -> int | None:
    """Locate an unqualified declaration in its defining module."""
    without_blocks = BLOCK_COMMENT.sub(
        lambda match: "\n" * match.group().count("\n"), text)
    tail = re.escape(name.rsplit(".", 1)[-1])
    keywords = "|".join(DECLARATION_KEYWORDS)
    pattern = re.compile(
        rf"\b(?:{keywords})\s+{tail}(?=\s|[:({{]|$)")
    matches = [
        number
        for number, raw in enumerate(without_blocks.split("\n"), start=1)
        if pattern.search(LINE_COMMENT.sub("", raw))
    ]
    return matches[0] if len(matches) == 1 else None


def conjecture_declarations() -> list[tuple[str, str, int]]:
    """Resolve graded conjecture declarations omitted from registry by-id."""
    if not CONJECTURES.is_file() or not DECLARATION_INDEX.is_file():
        missing = [
            path.relative_to(ROOT).as_posix()
            for path in (CONJECTURES, DECLARATION_INDEX)
            if not path.is_file()
        ]
        raise RuntimeError(f"missing conjecture input: {', '.join(missing)}")

    rows = json.loads(CONJECTURES.read_text())["conjectures"]
    declarations = json.loads(DECLARATION_INDEX.read_text())["declarations"]
    indexed_modules = {
        declaration["name"]: declaration["module"]
        for declaration in declarations
        if declaration.get("name") and declaration.get("module")
    }
    resolved: list[tuple[str, str, int]] = []
    unresolved: list[str] = []
    for row in rows:
        name = row.get("lean")
        if not name or not row.get("source_fidelity"):
            continue
        module = indexed_modules.get(name) or row.get("lean_module")
        if not module:
            unresolved.append(name)
            continue
        path = module.replace(".", "/") + ".lean"
        source = ROOT / path
        if not source.is_file():
            unresolved.append(name)
            continue
        line = declaration_line(source.read_text(encoding="utf-8"), name)
        if line is None:
            unresolved.append(name)
            continue
        resolved.append((name, path, line))
    if unresolved:
        raise RuntimeError(
            "could not resolve graded conjecture declaration(s): "
            + ", ".join(unresolved))
    return resolved


def current() -> dict[str, dict[str, str]]:
    """Signature hashes for every ledger declaration with a definition site."""
    index = json.loads(BY_ID.read_text())
    sources: dict[str, str] = {}
    out: dict[str, dict[str, str]] = {}
    for row in index["results_by_id"].values():
        artifact = row.get("lean_artifact") or {}
        for declaration in artifact.get("declarations") or []:
            name = declaration.get("atlas_declaration")
            path, line = declaration.get("file"), declaration.get("line")
            if not (name and path and line):
                continue  # vendored or external: no in-tree definition site
            if path not in sources:
                file = ROOT / path
                sources[path] = file.read_text(encoding="utf-8") if file.is_file() else ""
            statement = signature(sources[path], line)
            if statement is None:
                continue
            out[name] = {
                "file": path,
                "sha256": hashlib.sha256(statement.encode()).hexdigest()[:16],
            }
    for name, path, line in conjecture_declarations():
        if path not in sources:
            sources[path] = (ROOT / path).read_text(encoding="utf-8")
        statement = signature(sources[path], line)
        if statement is None:
            raise RuntimeError(f"could not extract signature for {name}")
        out[name] = {
            "file": path,
            "sha256": hashlib.sha256(statement.encode()).hexdigest()[:16],
        }
    for name, path in SPECIFICATION_SURFACES.items():
        source = ROOT / path
        if not source.is_file():
            raise RuntimeError(f"specification surface file is missing: {path}")
        if path not in sources:
            sources[path] = source.read_text(encoding="utf-8")
        line = declaration_line(sources[path], name)
        if line is None:
            raise RuntimeError(f"could not locate specification surface {name} in {path}")
        statement = signature(sources[path], line)
        if statement is None:
            raise RuntimeError(f"could not extract signature for {name}")
        out[name] = {
            "file": path,
            "sha256": hashlib.sha256(statement.encode()).hexdigest()[:16],
        }
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true",
                        help="record the current statements as the baseline")
    args = parser.parse_args()

    if not BY_ID.is_file():
        print(f"check_statement_freeze: missing {BY_ID}", file=sys.stderr)
        return 1
    try:
        now = current()
    except (KeyError, OSError, RuntimeError, json.JSONDecodeError) as error:
        print(f"check_statement_freeze: {error}", file=sys.stderr)
        return 1
    if not now:
        print("check_statement_freeze: no ledger declaration resolved to a "
              "signature — by-id.json or the tree moved under this script",
              file=sys.stderr)
        return 1

    if args.write:
        LOCK.write_text(json.dumps(
            {"generated_by": "scripts/check_statement_freeze.py --write",
             "note": "Signature hashes of ledger-graded statements. A diff here "
                     "is a schema event: say which way fidelity moved and "
                     "re-grade the row.",
             "count": len(now),
             "declarations": dict(sorted(now.items()))},
            indent=2) + "\n")
        print(f"statement lock written: {len(now)} statements -> "
              f"{LOCK.relative_to(ROOT)}")
        return 0

    if not LOCK.is_file():
        print(f"check_statement_freeze: no {LOCK.relative_to(ROOT)} yet — run "
              f"`python3 scripts/check_statement_freeze.py --write` once to "
              f"record the current statements.", file=sys.stderr)
        return 1

    locked = json.loads(LOCK.read_text())["declarations"]
    changed = sorted(n for n, v in now.items()
                     if n in locked and locked[n]["sha256"] != v["sha256"])
    added = sorted(set(now) - set(locked))
    gone = sorted(set(locked) - set(now))

    if not (changed or added or gone):
        print(f"check_statement_freeze ok: {len(now)} graded statements unchanged")
        return 0

    print(f"check_statement_freeze (advisory): {len(changed)} changed, "
          f"{len(added)} new, {len(gone)} no longer resolvable")
    for name in changed:
        print(f"  CHANGED  {name}\n           {now[name]['file']}")
    for name in added:
        print(f"  NEW      {name}")
    for name in gone:
        print(f"  GONE     {name}")
    if changed:
        print("\nA changed statement is a question, not a verdict: did fidelity "
              "move, and\nwhich way? Answer it in this change and re-grade the "
              "row if it did. Then run\n`--write` to record the new statements. "
              "See AGENTS.md § Statement freeze.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
