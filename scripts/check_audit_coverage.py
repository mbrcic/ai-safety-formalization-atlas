#!/usr/bin/env python3
"""Audit the public surface from the environment, and hold the regex audit to it.

``check_print_axioms.py`` decides *what* to audit by running two regular
expressions over source text.  ``check_every_module_audited`` already asserts
that no ``.lean`` file sits outside the audited set, so the file-level scope is
guarded — but nothing guarded the declaration level, and the two are not the
same thing.  A module can be in scope while a declaration *inside* it is
invisible to the pattern that was supposed to collect it.

That is not hypothetical.  ``PUBLIC_THEOREM_RE`` did not admit a leading
attribute, so every ``@[simp] public theorem`` in the tree matched nothing and
was never passed to ``#print axioms``.  The failure was silent by construction:
the audit reports how many names it *found*, and the v4.33.0 migration compared
that set against the pre-migration one name for name and called them identical
— which they were, because both sides were computed by the same regex and
inherited the same hole.  A check that derives the expected answer the same way
the subject does cannot find this class of bug.

So this script does not use the source text at all.  It walks the elaborated
environment, takes every public declaration under the ``AISafetyAtlas`` prefix,
drops the ones the compiler generated, and does two things with the remainder:

1. **Checks its axioms directly**, via ``Lean.collectAxioms`` in the same
   harness.  This is a second, independent implementation of the axiom audit,
   reaching the surface by a different route, so a hole in one is not a hole in
   both.  A declaration the regex never collected is still checked here.
2. **Reports what the regex audit failed to reach**, so the gap is a number
   someone has to look at rather than a silence.  Residue fails unless it is
   listed in ``docs/status/audit-coverage-exclusions.json`` with a reason.

**What "generated" means here, and why it is not a suffix list.**  Classifying
by name — ``.mk.inj``, ``.congr_simp``, ``.ext_iff`` and the rest — is the same
species of heuristic that produced the bug above.  The environment knows the
answer, so it is asked.  Three signals, no name parsing:

* ``findDeclarationRanges?`` is ``none`` — the declaration has no source syntax.
* ``isProjectionFn``, ``isAuxRecursor``, ``isRecCore``, ``isNoConfusion`` — the
  projection and recursor families.
* **Source-range sharing.**  ``deriving Fintype`` and ``@[ext]`` produce real
  declarations that carry a range, because they point back at the type's own
  syntax.  So a declaration is generated when some *other* declaration in its
  range group is an inductive: that is the type it was derived from.  An
  anonymous ``public instance : Foo := …`` is deliberately *not* caught by this
  — it owns its range, it is hand-written, and it can carry a ``sorry``, so it
  must be audited like anything else.

**Scope, matching what the regex audit claims.**  A facade module contributes
its ``public theorem`` and ``public lemma`` surface; its definitions are pinned
by ``check_public_api.py`` instead and exercised by the theorems above them.  A
consumer module contributes definitions too, because under the
answer-construction design a "determine X" problem *is* a ``def`` and its body
is the statement.  Clause 2 holds the regex to exactly that claim and no more;
clause 1 ignores the claim and checks everything public regardless.

Like the axiom audit and the declaration index, this runs through a generated
``lake env lean`` harness rather than a new ``lean_exe``, so the lakefile and
the build graph are untouched.
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import check_print_axioms as audit  # noqa: E402

PREFIX = "AISafetyAtlas"
ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
EXCLUSIONS_FILE = ROOT / "docs" / "status" / "audit-coverage-exclusions.json"

MARK_BEGIN = "ATLAS-AUDIT-COVERAGE-BEGIN"
MARK_END = "ATLAS-AUDIT-COVERAGE-END"
SEP = "\t"

# What `check_print_axioms.py` collects, by the kind the *environment* reports.
# `abbrev` and a non-class `instance` are both `def` there; `structure`, `class`
# and `inductive` are all `inductive`.
FACADE_KINDS = frozenset({"theorem"})
CONSUMER_KINDS = frozenset({"theorem", "def", "inductive"})


def harness_source() -> str:
    """A `run_cmd` reporting every public atlas constant, how it arose, and its axioms."""
    imports = ["import AISafetyAtlas"]
    imports += [f"import {module}" for module in audit.CONSUMER_MODULES]
    return "\n".join(
        [
            *imports,
            "import Lean",
            "",
            "/-! Generated coverage harness for scripts/check_audit_coverage.py.",
            "",
            "A plain `import` sees the public interface only, which is the surface",
            "the axiom audit is responsible for. -/",
            "",
            "open Lean Lean.Meta in",
            "run_cmd Lean.Elab.Command.liftTermElabM do",
            "  let env ← Lean.getEnv",
            "  let mut rows : Array String := #[]",
            "  for (n, ci) in env.constants.toList do",
            "    if n.isInternalDetail || n.hasMacroScopes then continue",
            f"    unless (`{PREFIX}).isPrefixOf n do continue",
            "    let kind :=",
            "      match ci with",
            "      | .thmInfo _ => \"theorem\"",
            "      | .axiomInfo _ => \"axiom\"",
            "      | .inductInfo _ => \"inductive\"",
            "      | .ctorInfo _ => \"constructor\"",
            "      | .recInfo _ => \"recursor\"",
            "      | .opaqueInfo _ => \"opaque\"",
            "      | .quotInfo _ => \"quot\"",
            "      | .defnInfo _ => \"def\"",
            # No source syntax, a projection, or the recursor family: generated
            # outright, and no range to report.
            "    let structural :=",
            "      env.isProjectionFn n || isAuxRecursor env n",
            "        || isRecCore env n || isNoConfusion env n",
            "    let range ← Lean.findDeclarationRanges? n",
            "    let rangeKey := match range with",
            "      | some r => s!\"{r.range.pos.line}:{r.range.pos.column}\"",
            "      | none => \"\"",
            "    let generated := structural || range.isNone",
            "    let isInst ← Lean.Meta.isInstance n",
            "    let axioms ← Lean.collectAxioms n",
            "    let axiomList := String.intercalate \",\" (axioms.toList.map toString)",
            "    let m := match env.getModuleFor? n with",
            "      | some mod => mod.toString",
            "      | none => \"\"",
            "    rows := rows.push",
            f'      s!"{{n}}{SEP}{{kind}}{SEP}{{m}}{SEP}{{generated}}{SEP}{{rangeKey}}'
            f'{SEP}{{isInst}}{SEP}{{axiomList}}"',
            f'  IO.println "{MARK_BEGIN}"',
            "  for r in rows.qsort (· < ·) do IO.println r",
            f'  IO.println "{MARK_END}"',
            "",
        ]
    )


def elaborate() -> list[dict]:
    with tempfile.TemporaryDirectory(prefix="atlas-coverage-") as tmp:
        harness = Path(tmp) / "AuditCoverage.lean"
        harness.write_text(harness_source(), encoding="utf-8")
        proc = subprocess.run(
            ["lake", "env", "lean", str(harness)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    blob = (proc.stdout or "") + "\n" + (proc.stderr or "")
    if proc.returncode != 0 or MARK_BEGIN not in blob:
        print(blob, file=sys.stderr)
        print(
            f"check_audit_coverage: lean failed (exit {proc.returncode})",
            file=sys.stderr,
        )
        raise SystemExit(1)
    body = blob.split(MARK_BEGIN, 1)[1].split(MARK_END, 1)[0]
    rows: list[dict] = []
    for line in body.splitlines():
        if not line.strip():
            continue
        parts = line.split(SEP)
        if len(parts) != 7:
            continue
        name, kind, module, generated, range_key, is_instance, axiom_list = parts
        rows.append(
            {
                "name": name,
                "kind": kind,
                "module": module,
                "generated": generated.strip() == "true",
                "range": range_key.strip(),
                "instance": is_instance.strip() == "true",
                "axioms": {a for a in axiom_list.split(",") if a},
            }
        )
    if not rows:
        print("check_audit_coverage: harness produced no rows", file=sys.stderr)
        raise SystemExit(1)
    return rows


def mark_derived(rows: list[dict]) -> None:
    """Flag declarations sharing a source range with an inductive as generated.

    `deriving Fintype` and `@[ext]` emit real declarations whose range points at
    the type's own syntax, so they are indistinguishable from hand-written ones
    by range alone -- but not by *company*. An anonymous `public instance` owns
    its range and stays hand-written, which is the case that must not be
    swallowed here: it can carry a `sorry`.
    """
    groups: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for row in rows:
        if row["range"]:
            groups[(row["module"], row["range"])].append(row)
    for group in groups.values():
        if len(group) < 2:
            continue
        anchors = [r for r in group if r["kind"] == "inductive"]
        if not anchors:
            continue
        anchor_names = {r["name"] for r in anchors}
        for row in group:
            if row["name"] not in anchor_names:
                row["generated"] = True


def load_exclusions() -> dict[str, str]:
    """`name -> reason` for declarations deliberately outside the regex audit."""
    if not EXCLUSIONS_FILE.is_file():
        return {}
    data = json.loads(EXCLUSIONS_FILE.read_text(encoding="utf-8"))
    return {entry["name"]: entry["reason"] for entry in data.get("exclusions", [])}


def main() -> int:
    facade = {
        str(path.relative_to(ROOT)).removesuffix(".lean").replace("/", ".")
        for path in audit.facade_sources()
    }
    consumer = set(audit.CONSUMER_MODULES)
    audited_names = set(audit.DECLARATIONS)
    exclusions = load_exclusions()

    rows = elaborate()
    mark_derived(rows)

    # Clause 1: axioms, checked from the environment for the whole public
    # surface, whether or not the regex audit ever reached it.
    dirty: list[str] = []
    checked = 0
    for row in rows:
        if row["generated"] or row["kind"] in {"constructor", "recursor", "quot"}:
            continue
        checked += 1
        extra = row["axioms"] - ALLOWED
        if extra:
            dirty.append(f"{row['name']}: extra axioms {sorted(extra)}")

    # Clause 2: whatever the regex audit claims to reach, it must reach.
    residue: list[dict] = []
    considered = 0
    for row in rows:
        if row["generated"]:
            continue
        module, kind, name = row["module"], row["kind"], row["name"]
        in_consumer = module in consumer
        if not in_consumer and module not in facade:
            # A module outside both closures is `check_every_module_audited`'s
            # business, not this script's; it fails there with a better message.
            continue
        if kind not in (CONSUMER_KINDS if in_consumer else FACADE_KINDS):
            continue
        # Lean names instances on the user's behalf. `public instance foo : C`
        # is collected by the pattern, but the anonymous `public instance : C`
        # that the atlas mostly writes has no source name to capture, and the
        # `deriving` clauses emit more of them. Holding a *text* pattern to a
        # name that never appears in the text is asking for a maintained list of
        # spellings, which is the failure this script exists to catch. Clause 1
        # checks their axioms from the environment, so nothing goes unchecked.
        if row["instance"]:
            continue
        considered += 1
        if name not in audited_names and name not in exclusions:
            residue.append(row)

    failed = False
    if dirty:
        print(
            f"check_audit_coverage: {len(dirty)} declaration(s) depend on axioms "
            "outside {propext, Classical.choice, Quot.sound}:",
            file=sys.stderr,
        )
        for line in sorted(dirty):
            print(f"  {line}", file=sys.stderr)
        failed = True

    if residue:
        print(
            f"check_audit_coverage: {len(residue)} public declaration(s) are "
            "inside the axiom audit's stated scope but were never collected by "
            "it. Either the patterns in check_print_axioms.py miss them, or "
            f"they belong in {EXCLUSIONS_FILE.relative_to(ROOT)} with a reason.",
            file=sys.stderr,
        )
        for row in sorted(residue, key=lambda r: r["name"]):
            print(
                f"  {row['kind']:9s} {row['name']}  ({row['module']})",
                file=sys.stderr,
            )
        failed = True

    if failed:
        return 1

    print(
        f"audit coverage ok: {checked} public declarations axiom-checked from "
        f"the environment; {considered} in the regex audit's stated scope, all "
        f"collected ({len(exclusions)} documented exclusion"
        f"{'' if len(exclusions) == 1 else 's'})"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
