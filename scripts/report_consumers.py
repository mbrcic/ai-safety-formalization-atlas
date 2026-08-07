#!/usr/bin/env python3
"""Report which atlas declarations something else actually depends on.

A result earns its place by making something else easier to state or prove. This
report says, per shipped declaration, whether anything does: nothing at all, an
`Examples/` use-site only, or a module that is itself doing mathematics.

That third tier is the one worth reading. `Examples/PublicAPI.lean` exercises
every declaration on the public root import as policy, so "has some consumer" is
true by construction and measures the policy rather than the work. "Consumed
outside `Examples/`" is not.

This is a **work queue, not a scoreboard**, and deliberately feeds no generated
view. An `Examples/`-only declaration is a candidate for the treatment CT-4 gave
`Verification.rice` and CT-16 gave the bounded portfolio target: give it a real
downstream consumer, or retire it. Either outcome is progress; the count itself
is not a target.

Accuracy, and the bias is deliberately conservative. A declaration counts as
used in a module when that module can see a definition site through the local
import graph *and* names it in code with comments and string literals masked.
Known limits:

* Matching is by leaf name, so two declarations sharing one (`Computability.rice`
  and its `Verification.rice` alias) treat each other's module as a definition
  site, and real use between them is invisible.
* `open`, dot-notation, and shadowing are not resolved the way the elaborator
  resolves them.

Both limits push the load-bearing count down rather than up, which is the right
direction for a queue: it will not tell you something is used when it is not.
Read it as an indicator, not a proof.

Usage:
    python3 scripts/report_consumers.py
    python3 scripts/report_consumers.py --queue    # only the work queue
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

from validate_current_state import (  # noqa: E402
    dependency_closure,
    lean_code_without_comments_or_strings,
    lean_module_name,
    local_imports,
)

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "registry.yaml"
LEAN_DIR = ROOT / "AISafetyAtlas"
EXAMPLES_PREFIX = "AISafetyAtlas.Examples"


def load_declarations() -> dict[str, str]:
    """Every atlas declaration in either ledger, mapped to its origin ID."""
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    declarations: dict[str, str] = {}
    for result in registry["results"]:
        artifact = result["lean_artifact"]
        if artifact is None:
            continue
        for declaration in artifact["declarations"]:
            declarations[declaration["atlas_declaration"]] = result["id"]
    return declarations


def lean_sources() -> dict[str, tuple[Path, str]]:
    # The root facade lives beside the directory, not inside it. Omitting it
    # severs the import graph: every Examples/ module reaches the atlas through
    # `import AISafetyAtlas`, so without the root nothing is visible from
    # anywhere and every declaration looks unused.
    paths = [ROOT / "AISafetyAtlas.lean", *sorted(LEAN_DIR.rglob("*.lean"))]
    return {
        lean_module_name(path): (path, lean_code_without_comments_or_strings(
            path.read_text(encoding="utf-8")
        ))
        for path in paths
    }


def visibility(sources: dict[str, tuple[Path, str]]) -> dict[str, set[str]]:
    """module -> every local module it can see through the import graph."""
    modules = set(sources)
    graph = {
        module: local_imports(code, modules) for module, (_, code) in sources.items()
    }
    return {module: dependency_closure(module, graph) for module in modules}


DEFINITION = "(?:theorem|lemma|def|abbrev|instance|structure|inductive)"


def definition_sites(leaf: str, sources: dict[str, tuple[Path, str]]) -> set[str]:
    """Modules that *define* `leaf`, not merely mention it.

    A declaration's namespace is not its module: `Preference.OverrideModel.foo`
    is proved in `Preference/Override.lean` and re-exported by the `Preference`
    facade. Deriving the home from the namespace makes the module that proves a
    theorem look like a module that consumes it, which inverts the whole report.
    """
    pattern = re.compile(
        rf"(?m)^\s*(?:public\s+|private\s+|protected\s+|noncomputable\s+)*"
        rf"{DEFINITION}\s+{re.escape(leaf)}(?![A-Za-z0-9_'])"
    )
    return {module for module, (_, code) in sources.items() if pattern.search(code)}


def consumers(
    declaration: str,
    sources: dict[str, tuple[Path, str]],
    visible: dict[str, set[str]],
) -> list[str]:
    """Modules that can see `declaration` and name it without defining it."""
    leaf = declaration.rsplit(".", 1)[1]
    homes = definition_sites(leaf, sources)
    if not homes:
        # Re-exported alias with no local definition site: fall back to the
        # longest module prefix of the declaration's own name.
        fallback = max(
            (m for m in sources if declaration.startswith(m + ".")),
            key=len,
            default="",
        )
        homes = {fallback} if fallback else set()
    pattern = re.compile(rf"(?<![A-Za-z0-9_.']){re.escape(leaf)}(?![A-Za-z0-9_'])")
    found = []
    for module, (_, code) in sources.items():
        if module in homes:
            continue
        if not homes & visible.get(module, set()):
            continue
        if declaration in code or pattern.search(code):
            found.append(module)
    return sorted(found)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--queue",
        action="store_true",
        help="print only the declarations with no consumer doing mathematics",
    )
    args = parser.parse_args()

    declarations = load_declarations()
    sources = lean_sources()
    visible = visibility(sources)

    load_bearing: list[tuple[str, str, list[str]]] = []
    examples_only: list[tuple[str, str, list[str]]] = []
    unused: list[tuple[str, str]] = []

    for declaration, origin in sorted(declarations.items()):
        found = consumers(declaration, sources, visible)
        if not found:
            unused.append((declaration, origin))
        elif all(module.startswith(EXAMPLES_PREFIX) for module in found):
            examples_only.append((declaration, origin, found))
        else:
            load_bearing.append((declaration, origin, found))

    if not args.queue:
        print(f"atlas declarations: {len(declarations)}")
        print(f"  consumed outside Examples/ : {len(load_bearing)}")
        print(f"  Examples/ use-site only    : {len(examples_only)}")
        print(f"  no consumer found          : {len(unused)}")
        print()

    print("Work queue — give it a downstream consumer, or retire it:")
    if not examples_only and not unused:
        print("  (empty)")
    for declaration, origin, _ in examples_only:
        print(f"  [{origin}] {declaration}  (Examples/ only)")
    for declaration, origin in unused:
        print(f"  [{origin}] {declaration}  (no consumer found)")

    if not args.queue and load_bearing:
        print()
        print("Load-bearing — something outside Examples/ depends on these:")
        for declaration, origin, found in load_bearing:
            short = ", ".join(m.replace("AISafetyAtlas.", "") for m in found[:3])
            more = f" (+{len(found) - 3})" if len(found) > 3 else ""
            print(f"  [{origin}] {declaration}\n      <- {short}{more}")


if __name__ == "__main__":
    main()
