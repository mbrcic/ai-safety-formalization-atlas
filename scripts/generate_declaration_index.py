#!/usr/bin/env python3
"""Emit the atlas's declaration index from the **elaborated environment**.

Every name check in this repository has been a regex over source text, and
``check_docstring_identifiers`` documents the price in its own header: *"a name
is accepted if it appears anywhere in Lean code, including as a ``have`` binder,
so a dangling reference survives if it happens to collide with one."*  That is
not a hypothetical.  A docstring naming a theorem that was renamed away still
passes if some unrelated proof happens to bind the old name.

The fix is to ask Lean instead of the file system.  This walks
``env.constants`` under the ``AISafetyAtlas`` prefix, exactly as CausalForge's
``LibraryIndexCore.buildEntries`` does for ``Causalean``, and writes name, kind
and module for every non-auxiliary declaration.  Module names are recorded too,
with kind ``module``: prose names a module as often as it names a theorem, and
a module with no public declarations of its own is otherwise invisible here.

**This is the public surface, not every declaration.**  The atlas uses the Lean
module system, and the harness imports the facade with a plain ``import``, so a
declaration written ``def foo`` rather than ``public def foo`` is not in the
imported interface and does not appear below.  That is a feature for the use
this index is put to — a docstring pointing at a name a consumer cannot type is
worth knowing about — but it means absence here is not evidence that a
declaration does not exist.  The consumer of this index treats a miss as
advisory for exactly that reason.

Two deliberate departures from that model.  It is run through a generated
``lake env lean`` harness rather than a new ``lean_exe``: ``check_print_axioms``
already establishes that idiom here, and it keeps the lakefile and the build
graph untouched.  And it records name, kind and module only — no statement, no
source slice, no axioms — because the axiom audit already exists and the index
is consumed by text checks that need resolution, not rendering.

The index is generated, never hand-edited.  Run with ``--write`` after adding or
renaming declarations; ``--check`` fails if the file on disk disagrees with the
environment, which is what the gate runs.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INDEX = ROOT / "docs" / "status" / "declaration-index.json"
PREFIX = "AISafetyAtlas"

# `Examples` and the conjecture modules are not reachable from the facade root,
# so the harness imports them explicitly. Same list the axiom audit consumes,
# and read from the same file so the two cannot drift.
BUILD_TARGETS = ROOT / "scripts" / "lean_build_targets.txt"

MARK_BEGIN = "ATLAS-DECL-INDEX-BEGIN"
MARK_END = "ATLAS-DECL-INDEX-END"


def consumer_modules() -> list[str]:
    if not BUILD_TARGETS.is_file():
        return []
    out: list[str] = []
    for raw in BUILD_TARGETS.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        out.append(line)
    return out


def harness_source() -> str:
    imports = ["import AISafetyAtlas", *[f"import {m}" for m in consumer_modules()]]
    return "\n".join(
        [
            *imports,
            "import Lean",
            "",
            "/-! Generated declaration index for scripts/generate_declaration_index.py.",
            "",
            "Walks the elaborated environment rather than the source text, so a name",
            "resolves here only if it is a real declaration. -/",
            "",
            "open Lean in",
            "run_cmd do",
            "  let env ← Lean.getEnv",
            "  let mut rows : Array String := #[]",
            "  for (n, ci) in env.constants.toList do",
            "    if n.isInternalDetail || n.hasMacroScopes then continue",
            f'    unless (`{PREFIX}).isPrefixOf n do continue',
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
            "    let m := match env.getModuleFor? n with",
            "      | some mod => mod.toString",
            "      | none => \"\"",
            "    rows := rows.push s!\"{n}\\t{kind}\\t{m}\"",
            "  for m in env.header.moduleNames do",
            f'    if (`{PREFIX}).isPrefixOf m then rows := rows.push s!"{{m}}\\tmodule\\t{{m}}"',
            f'  IO.println "{MARK_BEGIN}"',
            "  for r in rows.qsort (· < ·) do IO.println r",
            f'  IO.println "{MARK_END}"',
            "",
        ]
    )


AUX_SUFFIXES = {
    "mk", "rec", "recOn", "casesOn", "brecOn", "below", "ibelow", "ndrec",
    "noConfusion", "noConfusionType", "injEq", "sizeOf_spec", "toCtorIdx",
    "ofNat", "ctorIdx", "ctorElim", "ctorElimType", "ofNat_ctorIdx",
    "eq_def", "eq_1", "match_1", "proof_1",
}


def is_auxiliary(name: str) -> bool:
    """CausalForge's `isAuxiliary`, on the string form.

    Equation lemmas and structure projections' machinery are real constants but
    nothing writes prose about them, and including them would let a docstring
    'resolve' a name by colliding with generated noise.
    """
    parts = name.split(".")
    if any(p.startswith("_") for p in parts):
        return True
    if parts[-1] in AUX_SUFFIXES:
        return True
    return any(
        p.startswith("proof_") or p.startswith("eq_") and p[3:].isdigit()
        for p in parts[-1:]
    )


def elaborate() -> list[dict[str, str]]:
    with tempfile.TemporaryDirectory(prefix="atlas-declindex-") as tmp:
        harness = Path(tmp) / "DeclIndex.lean"
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
            "generate_declaration_index: lean failed "
            f"(exit {proc.returncode}); no index written",
            file=sys.stderr,
        )
        raise SystemExit(1)

    body = blob.split(MARK_BEGIN, 1)[1].split(MARK_END, 1)[0]
    rows: list[dict[str, str]] = []
    for line in body.splitlines():
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) != 3:
            continue
        name, kind, module = parts
        if is_auxiliary(name):
            continue
        rows.append({"name": name, "kind": kind, "module": module})
    return rows


def render(rows: list[dict[str, str]]) -> str:
    payload = {
        "schema_version": 1,
        "generated_by": "scripts/generate_declaration_index.py",
        "note": (
            "Declaration index walked from the elaborated environment, not from "
            "source text. Consumed by the prose checks so that a name resolves "
            "only when it is a real declaration."
        ),
        "prefix": PREFIX,
        "count": len(rows),
        "declarations": rows,
    }
    return json.dumps(payload, indent=2, ensure_ascii=False) + "\n"


def load_index() -> dict[str, str]:
    """`name -> kind` for every indexed declaration, or empty if absent."""
    if not INDEX.is_file():
        return {}
    data = json.loads(INDEX.read_text(encoding="utf-8"))
    return {d["name"]: d["kind"] for d in data.get("declarations", [])}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate the index")
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if the index on disk disagrees with the environment",
    )
    args = parser.parse_args()
    if not (args.write or args.check):
        parser.error("pass --write or --check")

    rendered = render(elaborate())
    if args.write:
        INDEX.write_text(rendered, encoding="utf-8")
        count = json.loads(rendered)["count"]
        print(f"declaration index written: {count} declarations -> "
              f"{INDEX.relative_to(ROOT)}")
        return 0

    current = INDEX.read_text(encoding="utf-8") if INDEX.is_file() else ""
    if current != rendered:
        print(
            "generate_declaration_index: "
            f"{INDEX.relative_to(ROOT)} is out of date; "
            "re-run scripts/generate_declaration_index.py --write",
            file=sys.stderr,
        )
        return 1
    print(f"declaration index ok: {json.loads(rendered)['count']} declarations")
    return 0


if __name__ == "__main__":
    sys.exit(main())
