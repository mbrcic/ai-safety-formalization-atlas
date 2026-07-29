#!/usr/bin/env python3
"""Kernel-level axiom check for every public theorem declared in facade modules.

Runs `lake env lean` on a generated `#print axioms` harness and asserts each
named declaration depends only on the standard classical Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`. This upgrades the textual
strict-trust grep to a kernel check for the complete theorem surface declared
by modules reachable through public `AISafetyAtlas.*` facade imports.
"""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ROOT_IMPORT = ROOT / "AISafetyAtlas.lean"
ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})

PUBLIC_IMPORT_RE = re.compile(r"^public import ([A-Za-z0-9_'.]+)\s*$")
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_'.]+)\s*$")
END_RE = re.compile(r"^\s*end\s+([A-Za-z0-9_'.]+)\s*$")
PUBLIC_THEOREM_RE = re.compile(
    r"^\s*public\s+theorem\s+([A-Za-z0-9_'.]+)\b"
)


def imported_atlas_modules(path: Path) -> list[str]:
    """Read public imports belonging to this package from one Lean module."""
    return [
        match.group(1)
        for line in path.read_text(encoding="utf-8").splitlines()
        if (match := PUBLIC_IMPORT_RE.match(line))
        if match.group(1).startswith("AISafetyAtlas")
    ]


def facade_sources() -> list[Path]:
    """Resolve the complete transitive public atlas facade closure."""
    pending = imported_atlas_modules(ROOT_IMPORT)
    if not pending:
        raise RuntimeError(f"no public imports found in {ROOT_IMPORT}")
    seen: set[str] = set()
    paths: list[Path] = []
    while pending:
        module = pending.pop(0)
        if module in seen:
            continue
        seen.add(module)
        path = ROOT / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            raise RuntimeError(
                f"public atlas import missing module: {path.relative_to(ROOT)}"
            )
        paths.append(path)
        pending.extend(imported_atlas_modules(path))
    return paths


def public_theorems_in(path: Path) -> list[str]:
    """Extract fully qualified `public theorem` names from one facade module.

    Facade files use explicit namespaces. Named `end` commands pop only matching
    namespaces; section endings such as `end Operations` are intentionally
    ignored.
    """
    namespace: list[str] = []
    declarations: list[str] = []
    for line_number, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if match := NAMESPACE_RE.match(line):
            name = match.group(1)
            components = name.split(".")
            if name.startswith("AISafetyAtlas."):
                namespace = components
            else:
                namespace.extend(components)
            continue
        if match := END_RE.match(line):
            name = match.group(1)
            if ".".join(namespace) == name:
                namespace.clear()
            elif namespace and namespace[-1] == name:
                namespace.pop()
            continue
        if match := PUBLIC_THEOREM_RE.match(line):
            if not namespace:
                relative = path.relative_to(ROOT)
                raise RuntimeError(
                    f"{relative}:{line_number}: public theorem outside a namespace"
                )
            declarations.append(".".join(namespace + [match.group(1)]))
    return declarations


def discover_public_theorems() -> list[str]:
    """Discover the complete theorem surface from all root facade modules."""
    declarations = [
        declaration
        for path in facade_sources()
        for declaration in public_theorems_in(path)
    ]
    duplicates = sorted(
        declaration
        for declaration in set(declarations)
        if declarations.count(declaration) > 1
    )
    if duplicates:
        raise RuntimeError(f"duplicate public theorem declarations: {duplicates}")
    if not declarations:
        raise RuntimeError("no public facade theorems discovered")
    return declarations


DECLARATIONS = discover_public_theorems()

# Lean 4 formats:
#   'Name' depends on axioms: [propext, Classical.choice, Quot.sound]
#   'Name' does not depend on any axioms
# The axiom list may wrap across lines after the opening bracket.
DECL_START = re.compile(
    r"^'(.+)' (depends on axioms|does not depend on any axioms):\s*(.*)$"
)
DECL_START_NO_COLON = re.compile(
    r"^'(.+)' (does not depend on any axioms)\s*$"
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
