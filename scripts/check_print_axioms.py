#!/usr/bin/env python3
"""Kernel-level axiom check for atlas headline declarations (R7-2 item 5).

Runs `lake env lean` on a generated `#print axioms` harness and asserts each
named declaration depends only on the standard classical Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`. This upgrades the textual
strict-trust grep to a kernel check for the public theorem surface.
"""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})

# Public atlas theorems that must stay axiom-clean. Keep in sync with the
# root-import surface exercised by Examples.PublicAPI / Registry.
DECLARATIONS = [
    "AISafetyAtlas.Computability.rice",
    "AISafetyAtlas.Computability.rice_code_iff",
    "AISafetyAtlas.Computability.halting_problem",
    "AISafetyAtlas.SocialChoice.arrow",
    "AISafetyAtlas.SocialChoice.Utility.arrow",
    "AISafetyAtlas.SocialChoice.gibbard_satterthwaite",
    "AISafetyAtlas.Logic.chaitin_incompleteness",
    "AISafetyAtlas.Logic.chaitin_bound",
    "AISafetyAtlas.Logic.godel_first_incompleteness",
    "AISafetyAtlas.Logic.godel_second_incompleteness",
    "AISafetyAtlas.Logic.tarski_undefinability",
    "AISafetyAtlas.Logic.loeb",
    "AISafetyAtlas.Explainability.attribution_impossibility",
    "AISafetyAtlas.Learning.no_free_lunch",
    "AISafetyAtlas.Learning.sum_performance_eq_scaled_sum",
    "AISafetyAtlas.Verification.rice",
    "AISafetyAtlas.Verification.AgentBehavior.no_behavioral_safety_verifier",
    "AISafetyAtlas.Verification.Robot.action_safety_unverifiable",
]

# Lean 4 formats:
#   'Name' depends on axioms: [propext, Classical.choice, Quot.sound]
#   'Name' does not depend on any axioms
# The axiom list may wrap across lines after the opening bracket.
DECL_START = re.compile(
    r"^'([^']+)' (depends on axioms|does not depend on any axioms):\s*(.*)$"
)
DECL_START_NO_COLON = re.compile(
    r"^'([^']+)' (does not depend on any axioms)\s*$"
)


def harness_source() -> str:
    lines = [
        "import AISafetyAtlas",
        "",
        "/-! Generated axiom harness for scripts/check_print_axioms.py. -/",
        "",
    ]
    for decl in DECLARATIONS:
        lines.append(f"#print axioms {decl}")
    lines.append("")
    return "\n".join(lines)


def parse_axioms(blob: str) -> dict[str, set[str]]:
    found: dict[str, set[str]] = {}
    lines = blob.splitlines()
    index = 0
    while index < len(lines):
        line = lines[index].strip()
        match = DECL_START.match(line) or DECL_START_NO_COLON.match(line)
        if not match:
            index += 1
            continue
        name = match.group(1)
        kind = match.group(2)
        rest = match.group(3) if match.lastindex >= 3 else ""
        if "does not depend" in kind:
            found[name] = set()
            index += 1
            continue
        # Accumulate until brackets balance (handles multi-line axiom lists).
        body = rest
        while body.count("[") > body.count("]") and index + 1 < len(lines):
            index += 1
            body += " " + lines[index].strip()
        body = body.strip()
        if body in {"", "[]"}:
            found[name] = set()
        else:
            inner = body.strip()
            if inner.startswith("["):
                inner = inner[1:]
            if inner.endswith("]"):
                inner = inner[:-1]
            axioms = {part.strip() for part in inner.split(",") if part.strip()}
            found[name] = axioms
        index += 1
    return found


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="atlas-axioms-") as tmp:
        harness = Path(tmp) / "PrintAxioms.lean"
        harness.write_text(harness_source(), encoding="utf-8")
        # lake env lean elaborates imports from the package root.
        proc = subprocess.run(
            ["lake", "env", "lean", str(harness)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    output = (proc.stdout or "") + "\n" + (proc.stderr or "")
    if proc.returncode != 0:
        print(output, file=sys.stderr)
        print(
            f"check_print_axioms: lean failed with exit {proc.returncode}",
            file=sys.stderr,
        )
        raise SystemExit(1)

    parsed = parse_axioms(output)
    missing = [name for name in DECLARATIONS if name not in parsed]
    if missing:
        print(output, file=sys.stderr)
        print(
            f"check_print_axioms: missing #print axioms lines for: {missing}",
            file=sys.stderr,
        )
        raise SystemExit(1)

    bad: list[str] = []
    for name in DECLARATIONS:
        axioms = parsed[name]
        extra = axioms - ALLOWED
        if extra:
            bad.append(f"{name}: extra axioms {sorted(extra)} (got {sorted(axioms)})")
    if bad:
        for line in bad:
            print(f"check_print_axioms: {line}", file=sys.stderr)
        raise SystemExit(1)

    print(
        f"check_print_axioms ok: {len(DECLARATIONS)} declarations ⊆ "
        f"{{propext, Classical.choice, Quot.sound}}"
    )


if __name__ == "__main__":
    main()
