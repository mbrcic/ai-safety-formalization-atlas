#!/usr/bin/env python3
"""Hold the statement-drift checker to the declarations the environment reports.

``check_statement_drift.py`` is the gate the migration argument rests on: it is
what says a version bump changed proofs and not statements. It reads source
text, and it decides where one declaration ends and the next begins with a
heuristic -- a line that starts in column zero whose first token is a known
declaration or context keyword. Anything that heuristic walks past is not
reported as changed, because it is not reported at all.

Nothing checked that. The axiom audit had the same shape of gap and it was real:
``PUBLIC_THEOREM_RE`` rejected a leading attribute, fifty-one declarations were
never audited, and the tests missed it because they pinned the *name* grammar
and never varied what preceded ``public``. ``check_audit_coverage.py`` closed
that by asking the elaborated environment what exists instead of asking the
regex what it matched. This does the same for the drift checker, which is now
the load-bearing gate with no independent cross-check.

**The specific failures this can catch.** They are not hypothetical shapes; each
is reachable from the code as written:

* a declaration indented off column zero, which ``starts_command`` skips;
* a declaration opened by a keyword missing from ``DECL_KINDS``;
* **namespace mis-tracking**, which is the interesting one. ``_blocks`` pops the
  namespace stack on a bare ``end``, so an unnamed ``section`` closing inside a
  namespace pops the namespace with it, and every declaration after that point
  is keyed under the wrong qualified name. A rename is a removal plus an
  addition, so a whole file's worth of declarations could silently be compared
  against nothing.

Comparison is by qualified name, which is what makes the third case visible: the
environment's name for a declaration is ground truth, so a unit keyed under the
wrong namespace shows up as a name the drift checker never produced.

**Private declarations are included.** ``import all`` is used rather than a plain
``import`` -- the drift checker sees the whole file, so a check on its coverage
that only looked at the public surface would leave the private half unguarded,
and the v4.33.0 migration added a private lemma. Lean reports these as
``_private.<Module>.<n>.<Name>``; the prefix is stripped to recover the name as
written.

**Anonymous instances are counted, not named.** ``public instance : Fintype X``
has no source name, so the drift checker keys it as ``<anonymous>`` and the
environment calls it ``instFintypeX``; the two cannot be matched by name. They
are compared per module by count instead, which still catches one going missing.

Residue fails unless listed in ``docs/status/drift-coverage-exclusions.json``
with a reason.

Usage:
    python3 scripts/check_drift_coverage.py
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import check_audit_coverage as coverage  # noqa: E402
import check_print_axioms as audit  # noqa: E402
import check_statement_drift as drift  # noqa: E402

PREFIX = "AISafetyAtlas"
EXCLUSIONS_FILE = ROOT / "docs" / "status" / "drift-coverage-exclusions.json"

MARK_BEGIN = "ATLAS-DRIFT-COVERAGE-BEGIN"
MARK_END = "ATLAS-DRIFT-COVERAGE-END"
SEP = "\t"

# `_private.AISafetyAtlas.Causal.Model.0.helper` -> `helper`, which is the name
# the source actually writes and therefore the name the drift checker keys on.
PRIVATE_RE = re.compile(r"^_private\.(?P<module>[^.].*?)\.\d+\.(?P<name>.+)$")

# Constructors and recursors are consequences of an `inductive`, not separate
# source declarations, and the drift checker rightly emits nothing for them.
NOT_SOURCE_KINDS = frozenset({"constructor", "recursor", "quot"})

# Source commands that declare something without giving it a name Lean will
# reuse. `notation` names its constant `«term_≻[_]_»`; the drift checker keys
# the command by its first token, which for a notation is a parameter. Both are
# tracking the same command, so they are reconciled by count rather than name.
UNNAMED_COMMAND_KINDS = frozenset({
    "notation", "syntax", "macro", "macro_rules", "elab", "elab_rules",
    "infixl", "infixr", "infix", "prefix", "postfix", "declare_syntax_cat",
    "instance",
})


def _built_modules(root: Path) -> list[str]:
    """Modules under `root` that have a compiled artifact and a source file."""
    build = root / ".lake" / "build" / "lib" / "lean" / PREFIX
    modules = [PREFIX] if (build.parent / f"{PREFIX}.olean").is_file() else []
    modules += [
        name
        for path in sorted(build.rglob("*.olean"))
        for name in [
            f"{PREFIX}." + str(path.relative_to(build)).removesuffix(".olean").replace("/", ".")
        ]
        if (root / (name.replace(".", "/") + ".lean")).is_file()
    ]
    return modules


def built_modules(root: Path | None = None) -> list[str]:
    """Every atlas module with a compiled artifact, each named explicitly.

    Naming all of them matters and the reason is not obvious. `import all` is
    transitive for *constants* but not for *declaration ranges*: a module reached
    only through another module's import contributes its declarations with
    `findDeclarationRanges?` returning `none`. Importing the root plus the consumer
    targets gets ranges for 68 modules out of 195, so the 3965 declarations in
    the rest are classified range-less, treated as compiler-generated and
    skipped -- a coverage check that silently covers a third of the tree while
    reporting a large, healthy-looking number.

    Discovery is by build artifact rather than by source file so that a `.lean`
    which is not part of any target cannot quietly become an import error.

    A module is ours when it has both a compiled artifact and a source. Lake does
    not prune build output for a source that no longer exists, and a restored
    build cache carries those orphans across a rename or a consolidation; they
    fail to load with "incompatible header", which reads as a broken tree rather
    than as the stale artifact it is. Requiring the artifact keeps the property
    above; requiring the source drops the orphans, and the two together are the
    modules this tree actually compiles.
    """
    return _built_modules(root or ROOT)


def harness_source(modules: list[str]) -> str:
    """A `run_cmd` reporting every atlas constant, including the private ones.

    `import all` needs a `module` header.
    """
    imports = [f"import all {module}" for module in modules]
    return "\n".join(
        [
            "module",
            *imports,
            "import Lean",
            "",
            "/-! Generated coverage harness for scripts/check_drift_coverage.py. -/",
            "",
            "open Lean Lean.Meta in",
            "run_cmd Lean.Elab.Command.liftTermElabM do",
            "  let env ← Lean.getEnv",
            "  let mut rows : Array String := #[]",
            "  for (n, ci) in env.constants.toList do",
            "    if n.isInternalDetail || n.hasMacroScopes then continue",
            # `toString n` is ambiguous under `open Lean Lean.Meta` once enough
            # namespaces are in scope; the interpolation is not.
            '    let s := s!"{n}"',
            f'    unless (`{PREFIX}).isPrefixOf n || s.startsWith "_private.{PREFIX}" do',
            "      continue",
            "    let kind :=",
            "      match ci with",
            '      | .thmInfo _ => "theorem"',
            '      | .axiomInfo _ => "axiom"',
            '      | .inductInfo _ => "inductive"',
            '      | .ctorInfo _ => "constructor"',
            '      | .recInfo _ => "recursor"',
            '      | .opaqueInfo _ => "opaque"',
            '      | .quotInfo _ => "quot"',
            '      | .defnInfo _ => "def"',
            "    let structural :=",
            "      env.isProjectionFn n || isAuxRecursor env n",
            "        || isRecCore env n || isNoConfusion env n",
            "    let range ← Lean.findDeclarationRanges? n",
            "    let rangeKey := match range with",
            '      | some r => s!"{r.range.pos.line}:{r.range.pos.column}"',
            '      | none => ""',
            # The *end* of the declaration's syntax, which is what makes the
            # containment test below possible: a `deriving` instance or an
            # `@[ext]` theorem starts inside the span of the type it came from.
            "    let endKey := match range with",
            '      | some r => s!"{r.range.endPos.line}:{r.range.endPos.column}"',
            '      | none => ""',
            "    let generated := structural || range.isNone",
            "    let isInst ← Lean.Meta.isInstance n",
            "    let m := match env.getModuleFor? n with",
            "      | some mod => mod.toString",
            '      | none => ""',
            "    rows := rows.push",
            f'      s!"{{n}}{SEP}{{kind}}{SEP}{{m}}{SEP}{{generated}}{SEP}{{rangeKey}}'
            f'{SEP}{{endKey}}{SEP}{{isInst}}"',
            f'  IO.println "{MARK_BEGIN}"',
            "  for r in rows.qsort (· < ·) do IO.println r",
            f'  IO.println "{MARK_END}"',
            "",
        ]
    )


def elaborate(modules: list[str]) -> list[dict]:
    with tempfile.TemporaryDirectory(prefix="atlas-drift-coverage-") as tmp:
        harness = Path(tmp) / "DriftCoverage.lean"
        harness.write_text(harness_source(modules), encoding="utf-8")
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
        print(f"check_drift_coverage: lean failed (exit {proc.returncode})", file=sys.stderr)
        raise SystemExit(1)
    body = blob.split(MARK_BEGIN, 1)[1].split(MARK_END, 1)[0]
    rows: list[dict] = []
    for line in body.splitlines():
        if not line.strip():
            continue
        parts = line.split(SEP)
        if len(parts) != 7:
            continue
        name, kind, module, generated, range_key, end_key, is_instance = parts
        rows.append(
            {
                "name": name,
                "kind": kind,
                "module": module,
                "generated": generated.strip() == "true",
                "range": range_key.strip(),
                "end": end_key.strip(),
                "instance": is_instance.strip() == "true",
            }
        )
    if not rows:
        print("check_drift_coverage: harness produced no rows", file=sys.stderr)
        raise SystemExit(1)
    return rows


def _position(key: str) -> tuple[int, int] | None:
    if not key or ":" not in key:
        return None
    line, _, column = key.partition(":")
    try:
        return (int(line), int(column))
    except ValueError:
        return None


def mark_contained(rows: list[dict]) -> None:
    """Flag a declaration whose syntax begins inside another declaration's span.

    This is what `deriving` and `@[ext]` produce. Their ranges point back into
    the type they came from -- ``instDecidableEqCandIx`` at ``194:11`` sits
    inside ``inductive CandIx`` at ``189:0`` -- so they carry a real range and
    look hand-written to any test that only asks whether a range exists.

    ``check_audit_coverage.mark_derived`` catches the narrower case where the
    ranges are *equal*; containment generalises it, which is why the seven names
    that file has to exclude by hand are classified correctly here.

    Deliberately *not* a column test. "Starts in column zero" would classify
    these correctly too, and it is exactly the assumption `starts_command` makes
    -- the assumption this script exists to check. Reusing it here would make the
    check agree with the drift checker by construction, which is the failure mode
    that produced the bug this whole line of work came from.
    """
    by_module: dict[str, list[dict]] = defaultdict(list)
    for row in rows:
        if row["range"] and row["end"]:
            by_module[row["module"]].append(row)
    for group in by_module.values():
        spans = []
        for row in group:
            start, stop = _position(row["range"]), _position(row["end"])
            if start and stop and start < stop:
                spans.append((start, stop, row))
        for start, _stop, row in spans:
            for other_start, other_stop, other in spans:
                if other is row:
                    continue
                if other_start < start < other_stop:
                    row["generated"] = True
                    break


def source_name(row: dict) -> str:
    """The declaration's name as the source writes it, private mangling removed."""
    match = PRIVATE_RE.match(row["name"])
    if not match:
        return row["name"]
    return match.group("name")


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def unnameable(name: str) -> bool:
    """Whether Lean had to escape this name, so no source declaration wrote it.

    Lean renders a `Name` with guillemets exactly when a component is not a legal
    identifier, which is the case for the constant a `notation` command produces.
    The test is therefore Lean's own answer to "could this have been written as a
    declaration name", not a guess about how such names tend to look.
    """
    return "«" in name


def drift_names(path: Path) -> tuple[set[str], int]:
    """Qualified names the drift checker keys on, and its unnamed-command count.

    The second number counts the units the drift checker tracks but cannot label
    with a name the environment would recognise: anonymous declarations, and the
    syntax-declaring commands whose first token is a parameter rather than a name.
    """
    text = path.read_text(encoding="utf-8")
    named: set[str] = set()
    unnamed = 0
    for kind, qualified, _ordinal, _block in drift._blocks(text):
        if qualified.endswith("<anonymous>") or kind in UNNAMED_COMMAND_KINDS:
            unnamed += 1
        if not qualified.endswith("<anonymous>"):
            named.add(qualified)
    return named, unnamed


def load_exclusions() -> dict[str, str]:
    """`name -> reason` for declarations the drift checker deliberately misses."""
    if not EXCLUSIONS_FILE.is_file():
        return {}
    data = json.loads(EXCLUSIONS_FILE.read_text(encoding="utf-8"))
    return {entry["name"]: entry["reason"] for entry in data.get("exclusions", [])}


def main() -> int:
    modules = built_modules()
    if len(modules) < 100:
        print(
            f"check_drift_coverage: only {len(modules)} built modules found under "
            f".lake/build/lib/lean/{PREFIX} — run `lake build` first",
            file=sys.stderr,
        )
        return 1
    rows = elaborate(modules)
    coverage.mark_derived(rows)
    mark_contained(rows)

    by_module: dict[str, list[dict]] = defaultdict(list)
    for row in rows:
        if row["generated"] or row["kind"] in NOT_SOURCE_KINDS:
            continue
        by_module[row["module"]].append(row)

    exclusions = load_exclusions()
    missing: list[str] = []
    unreadable: list[str] = []
    instance_gaps: list[str] = []
    checked = 0

    for module, declarations in sorted(by_module.items()):
        path = module_path(module)
        if not path.is_file():
            unreadable.append(f"  {module}: no source at {path.relative_to(ROOT)}")
            continue
        named, unnamed_units = drift_names(path)

        env_unnamed = 0
        for row in declarations:
            name = source_name(row)
            if name in named:
                checked += 1
                continue
            if unnameable(row["name"]) or row["instance"]:
                # The source never wrote this name -- an anonymous `instance`, or
                # the constant behind a `notation`. The drift checker tracks the
                # command; it just cannot label it with the environment's name.
                # Reconciled by count below.
                env_unnamed += 1
                continue
            checked += 1
            if row["name"] in exclusions or name in exclusions:
                continue
            missing.append(f"  {row['kind']:<10} {row['name']}\n             {module}")

        if env_unnamed > unnamed_units:
            instance_gaps.append(
                f"  {module}: {env_unnamed} unnamed declaration(s) in the environment, "
                f"{unnamed_units} unnamed unit(s) in the drift checker"
            )

    if unreadable:
        print("check_drift_coverage: module with no source file", file=sys.stderr)
        for line in unreadable:
            print(line, file=sys.stderr)
        return 1

    if missing or instance_gaps:
        print(
            f"check_drift_coverage: {len(missing) + len(instance_gaps)} declaration(s) "
            "the environment reports and check_statement_drift.py does not key.\n"
            "A declaration it cannot key is one it cannot report as changed, so a "
            "statement could move underneath it without the gate noticing.",
            file=sys.stderr,
        )
        for line in missing:
            print(line, file=sys.stderr)
        for line in instance_gaps:
            print(line, file=sys.stderr)
        print(
            "\nEither fix the block/namespace tracking in check_statement_drift.py, "
            f"or record the name in {EXCLUSIONS_FILE.relative_to(ROOT)} with a reason.",
            file=sys.stderr,
        )
        return 1

    note = f" ({len(exclusions)} documented exclusions)" if exclusions else ""
    print(
        f"drift coverage ok: {checked} declarations from the environment across "
        f"{len(by_module)} modules, all keyed by check_statement_drift.py{note}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
