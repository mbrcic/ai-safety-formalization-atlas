#!/usr/bin/env python3
"""Elaborate every deposited intake statement and check it is a proposition.

`validate_intake.py` enforces the lane's *shape*: the row's fields, the refused
grade columns, the containment prefix, and that the deposited name resolves in
the elaborated declaration index with the right kind and module. It stops there
for a reason -- the index records name, kind and module and no types, which is a
decision `generate_declaration_index.py` argues for in its own header.

So the lane's headline promise, **"a compiling `Prop`"**, was checked by nobody.
An adversarial review on 2026-09-07 deposited

    public def AISafetyAtlas.Conjectures.Intake.Example.notAProposition : Nat := 7

against a fixture row and watched the validator report `intake ok`. A `Nat` is
not a statement, and a lane that admits one is not an intake lane. This script
is the missing half.

It works the way `check_print_axioms.py` and `generate_declaration_index.py`
already do here: write a harness, run it through `lake env lean`, read what Lean
says. Two things are established per row, and both need elaboration rather than
text:

* the deposited name's type is `∀ ..., Prop` -- a parameterised statement is
  still a statement, so the check telescopes the binders and asks whether the
  result is `Prop`, rather than demanding the bare type be `Prop`;
* the name is *reachable* from the module the row advertises, because the
  harness imports that module and nothing else.

This is a check on the *kind* of thing deposited, never on what it says. A
`def foo : Prop := True` passes and asserts nothing, which is correct for a lane
whose whole point is that grading happens later and by a human. "A compiling
`Prop`" is the promise, and a compiling `Prop` is exactly what this establishes.

Reachability, not authorship: a module that transitively imports the statement's
real home reaches it perfectly well, so this does not establish that the
advertised module is where the statement lives. `validate_intake.py` pins that
separately, by comparing the row against the declaration index's `module` field.
The two together are the check; either alone is not. What this half catches is
the case the other cannot see at all — an advertised module that does not reach
the statement, which makes the row's import instruction useless to a reader.

**Where it runs.** The Lean CI job, after the build, beside
`check_print_axioms.py`. Not `agent_gate.sh`: that gate's contract is schema,
generated views and path checks with no build, and its CI job installs pytest
and no toolchain. Putting it there on the reasoning that an empty lane costs
nothing was true and beside the point — the first real submission would have met
a missing `lake` instead of a verdict.

Usage:
    python3 scripts/check_intake_statements.py
"""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Any, NoReturn

ROOT = Path(__file__).resolve().parents[1]
INTAKE = ROOT / "intake.yaml"

sys.path.insert(0, str(Path(__file__).resolve().parent))

from validate_intake import require_mapping  # noqa: E402


HARNESS_PRELUDE = """
open Lean Meta

/-- `true` when the declaration's type telescopes to `Prop`. -/
def intakeIsStatement (n : Name) : MetaM Bool := do
  let some ci := (← getEnv).find? n | return false
  forallTelescopeReducing ci.type fun _ body => do
    return (← whnf body).isProp

def intakeCheck (n : Name) : MetaM Unit := do
  if (← getEnv).find? n |>.isNone then
    throwError "intake: {n} does not exist in the environment reached through its declared module"
  unless ← intakeIsStatement n do
    let some ci := (← getEnv).find? n | throwError "intake: {n} vanished"
    throwError "intake: {n} has type {ci.type}, which does not land in Prop; \
the lane takes a statement, not a value"
"""


def fail(message: str) -> NoReturn:
    print(f"check_intake_statements: {message}", file=sys.stderr)
    raise SystemExit(1)


def load_rows() -> list[dict[str, Any]]:
    if not INTAKE.is_file():
        fail("intake.yaml is missing")
    try:
        data = json.loads(INTAKE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(f"intake.yaml is unreadable: {error}")
    rows = require_mapping(data, "intake.yaml must contain an object").get("intake")
    if not isinstance(rows, list):
        fail("intake must be a list")
    return [require_mapping(row, "intake entries must be objects") for row in rows]


def harness_for(module: str, rows: list[dict[str, Any]]) -> str:
    """A harness for **one** advertised module and the rows that advertise it.

    One module per harness, not one harness for all of them. Importing every
    row's module into a single environment lets one row's import satisfy
    another row's name: a row advertising `Fairness.RiskAssignment` for
    `Knowledge.Knowable` passed, because a second row imported
    `AISafetyAtlas.Knowledge` and the union reached it. The check reported
    success "through the module each row advertises", which was false.

    `import Lean` is explicit rather than inherited. The harness uses `MetaM`,
    and every module reached in testing happened to pull Lean in through
    Mathlib — so a *minimal* deposit, `module` plus `public def s : Prop := True`
    with no imports of its own, made the harness fail with
    `identifier MetaM is unknown` on a statement that was perfectly valid.
    """
    lines = [f"import {module}", "import Lean", HARNESS_PRELUDE]
    for row in rows:
        lines.append(f"#eval intakeCheck `{row['lean']}")
    return "\n".join(lines) + "\n"


def main() -> int:
    rows = load_rows()
    if not rows:
        print(
            "check_intake_statements ok: the lane is empty, so there is no "
            "statement to elaborate — the check is live and has nothing to do"
        )
        return 0

    by_module: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        by_module.setdefault(str(row["lean_module"]), []).append(row)

    with tempfile.TemporaryDirectory(prefix="atlas-intake-") as tmp:
        for index, (module, module_rows) in enumerate(sorted(by_module.items())):
            path = Path(tmp) / f"IntakeProbe{index}.lean"
            path.write_text(harness_for(module, module_rows), encoding="utf-8")
            try:
                proc = subprocess.run(
                    ["lake", "env", "lean", str(path)],
                    cwd=ROOT, capture_output=True, text=True,
                )
            except FileNotFoundError:
                # Say which check cannot run and why, rather than raising a
                # traceback out of a validator. This check belongs to the Lean
                # CI job for exactly this reason: the cheap gate's runner has no
                # toolchain, and a deposited row must not be admitted by an
                # unavailable one either.
                fail(
                    "lake is not on PATH, so the deposited statements cannot be "
                    "elaborated. This check needs the build: run it after "
                    "`lake build`, or let the Lean CI job run it"
                )
            output = (proc.stdout + proc.stderr).strip()
            if proc.returncode != 0 or "error" in output:
                named = ", ".join(r["id"] for r in module_rows)
                fail(
                    f"{named}: at least one statement advertised as living in "
                    f"{module} did not elaborate as a proposition through it:"
                    f"\n{output}"
                )
    print(
        f"check_intake_statements ok: {len(rows)} deposited statement(s) across "
        f"{len(by_module)} module(s) elaborate to Prop, each through the module "
        "its own row advertises and nothing else"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
