#!/usr/bin/env python3
"""Kernel-level axiom check for the public theorem surface of the facade closure.

Runs `lake env lean` on a generated `#print axioms` harness and asserts each
named declaration depends only on the standard classical Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`. This upgrades the textual
strict-trust grep to a kernel check.

Scope, stated exactly, because an earlier version claimed more than it did:
every `public theorem` and `public lemma` declared inside a namespace in a
module reachable through public `AISafetyAtlas.*` facade imports, **plus** the
facades named in `OFF_ROOT_FACADES` and their own public closures. Declarations
introduced any other way are outside it — so `check_ledger_coverage` asserts
that every declaration the registry publishes falls inside, rather than leaving
that to the coincidence that published results happen to use these keywords.
"""

from __future__ import annotations

import json
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
# `lemma` is `theorem` under a different keyword: same kernel status, same
# public surface, same obligation. Matching only `theorem` audited 208 of the
# 325 public declarations in the facade closure and called that "the complete
# theorem surface".
# Match the whole name up to whatever delimits it, rather than an ASCII-only
# character class.  Two defects came from the earlier
# `([A-Za-z0-9_'.]+)\\b` form, and both were silent:
#
# * a name ending in a prime (`foo'`) has no word boundary after the quote, so
#   the match backtracked and truncated to `foo` — `foo` and `foo'` then
#   collapsed to one name and one of them was never checked;
# * a name containing a subscript (`F₁_of_compatible`) could not be matched at
#   all, because the class stops at `F` and `\\b` then fails against the
#   subscript, which Python counts as a word character.  Such declarations were
#   dropped from the scan entirely.
#
# Lean identifiers admit Greek letters, subscripts, `!`, `?` and more, so
# enumerating them is the wrong approach; the delimiters are the short list.
PUBLIC_THEOREM_RE = re.compile(
    r"^\s*public\s+(?:theorem|lemma)\s+([^\s:({\[]+)"
)


def imported_atlas_modules(path: Path) -> list[str]:
    """Read public imports belonging to this package from one Lean module."""
    return [
        match.group(1)
        for line in path.read_text(encoding="utf-8").splitlines()
        if (match := PUBLIC_IMPORT_RE.match(line))
        if match.group(1).startswith("AISafetyAtlas")
    ]


# Public facades deliberately kept off the root import, each with the reason.
#
# The audited surface is "what the ledger publishes", not "what the root import
# happens to re-export". Those coincided until a facade had a reason not to be
# re-exported. Without this list such a facade could publish declarations that
# no kernel audit ever reached, and `check_ledger_coverage` below would reject
# the row rather than the gap.
OFF_ROOT_FACADES: dict[str, str] = {
    "AISafetyAtlas.Oversight.Debate": (
        "re-exports a vendored root-namespace development; see the module "
        "docstring and vendor/debate/PROVENANCE.md"
    ),
}


def facade_sources() -> list[Path]:
    """Resolve the complete transitive public atlas facade closure."""
    pending = imported_atlas_modules(ROOT_IMPORT)
    if not pending:
        raise RuntimeError(f"no public imports found in {ROOT_IMPORT}")
    pending.extend(OFF_ROOT_FACADES)
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


BUILD_TARGETS = ROOT / "scripts" / "lean_build_targets.txt"


def consumer_sources() -> list[Path]:
    """Explicit build targets that the root facade deliberately does not import.

    The conjecture layer is a *consumer* of the atlas, not part of it: an
    unproved `Prop` must not sit on the public surface, and
    ``validate_conjectures.py`` fails if one becomes reachable from the root.
    That keeps those modules out of ``facade_sources`` — but axiom hygiene is a
    property of any checked theorem, whoever owns it, so they are audited here
    even though ``check_public_api.py`` correctly declines to pin them. Pinning
    would invent a stability contract for code nothing downstream may depend on.
    """
    facade = set(facade_sources())
    modules = [
        line.strip()
        for line in BUILD_TARGETS.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    paths = []
    for module in modules:
        path = ROOT / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            raise RuntimeError(f"build target names missing module: {module}")
        if path not in facade:
            paths.append(path)
    return paths


CONSUMER_MODULES = [
    str(path.relative_to(ROOT)).removesuffix(".lean").replace("/", ".")
    for path in consumer_sources()
]


def discover_public_theorems() -> list[str]:
    """Discover the audited theorem surface: the facade plus explicit consumers."""
    declarations = [
        declaration
        for path in list(facade_sources()) + consumer_sources()
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


def ledger_declarations() -> list[str]:
    """Every atlas declaration the registry publishes as a result."""
    registry = json.loads((ROOT / "registry.yaml").read_text(encoding="utf-8"))
    return [
        declaration["atlas_declaration"]
        for result in registry["results"]
        if result.get("lean_artifact")
        for declaration in result["lean_artifact"]["declarations"]
    ]


def check_ledger_coverage() -> None:
    """Every published declaration must be inside the audited set.

    Until this check existed, that held by coincidence: the audit collects names
    by scanning for a keyword, and every published result happened to be spelled
    with the one keyword it scanned for. A result declared any other way would
    have dropped out of the kernel audit while `Examples/Registry.lean` still
    `#check`ed it and the gate still reported green.
    """
    audited = set(DECLARATIONS)
    missing = sorted(set(ledger_declarations()) - audited)
    if missing:
        print(
            "check_print_axioms: registry declarations outside the audited "
            f"surface: {missing}",
            file=sys.stderr,
        )
        raise SystemExit(1)

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
    harness_imports = dict.fromkeys(
        ["AISafetyAtlas", *OFF_ROOT_FACADES, *CONSUMER_MODULES]
    )
    lines = [
        *[f"import {module}" for module in harness_imports],
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
        rest = match.group(3) if (match.lastindex or 0) >= 3 else ""
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
    # Cheap and first: no point spending a Lean elaboration to audit a set that
    # does not contain everything the ledger publishes.
    check_ledger_coverage()
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
