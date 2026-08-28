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

* Matching accepts any dotted *suffix* of a declaration's own name, so all three
  ways Lean lets a consumer write it count: `foo`, `Knowledge.foo`, and
  `AISafetyAtlas.Knowledge.foo`. `Other.foo` does not — it is a different `foo`.
* Definition sites are still found by leaf name, so two declarations sharing one
  (`Computability.rice` and its `Verification.rice` alias) treat each other's
  module as a definition site, and real use between them is invisible.
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
    """Every atlas declaration in the registry ledger, mapped to its owning ID.

    `validate_registry.py` enforces one owner per declaration. Assigning here
    rather than overwriting keeps that guarantee visible: if the invariant ever
    breaks, this raises instead of silently attributing the declaration to
    whichever row happened to be serialized last.
    """
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    declarations: dict[str, str] = {}
    for result in registry["results"]:
        artifact = result["lean_artifact"]
        if artifact is None:
            continue
        for declaration in artifact["declarations"]:
            name = declaration["atlas_declaration"]
            owner = declarations.setdefault(name, result["id"])
            if owner != result["id"]:
                raise SystemExit(
                    f"report_consumers: {name} is claimed by both {owner} and "
                    f"{result['id']}; run scripts/validate_registry.py"
                )
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


def qualified_forms(declaration: str) -> list[str]:
    """Every dotted suffix of `declaration`, longest first.

    Lean lets a consumer name a declaration three ways, and all three are uses:
    fully (`AISafetyAtlas.Knowledge.foo`), relative to an enclosing namespace
    (`Knowledge.foo`), or bare (`foo`). Matching only the leaf missed the middle
    form — the idiomatic one — because a dot precedes it; matching only the full
    name missed it too. Every declaration reached that way was reported unused.

    Suffixes, not substrings: `Other.foo` is a different `foo`, not a use of
    this one, and must not count.
    """
    parts = declaration.split(".")
    return [".".join(parts[index:]) for index in range(len(parts))]


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
    # Longest form first, so a fully-qualified use matches as a whole rather
    # than leaving a stray prefix. The lookbehind still forbids a preceding dot,
    # which is what keeps `Other.foo` out; the alternation is what lets
    # `Knowledge.foo` in. The lookahead keeps `foo_aux` out — including when it
    # is written fully qualified, which a raw substring test let through.
    pattern = re.compile(
        r"(?<![A-Za-z0-9_.'])(?:"
        + "|".join(re.escape(form) for form in qualified_forms(declaration))
        + r")(?![A-Za-z0-9_'])"
    )
    found = []
    for module, (_, code) in sources.items():
        if module in homes:
            continue
        if not homes & visible.get(module, set()):
            continue
        if pattern.search(code):
            found.append(module)
    return sorted(found)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--json",
        metavar="PATH",
        help="write the report as JSON to PATH (the generated view agents read; "
             "this script takes minutes, docs/status/consumers.json does not)",
    )
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

    if args.json:
        # The whole point of this file is that reading it costs a few kilobytes
        # while recomputing it costs minutes: the scan is quadratic in the
        # corpus. Keys are fully qualified so a consumer can look one up
        # without knowing which module defines it.
        payload = {
            "generated_by": "scripts/report_consumers.py --json",
            "counts": {
                "declarations": len(declarations),
                "load_bearing": len(load_bearing),
                "examples_only": len(examples_only),
                "no_consumer": len(unused),
            },
            "declarations": {},
            "work_queue": [],
        }
        for declaration, origin, found in load_bearing:
            payload["declarations"][declaration] = {
                "origin": origin, "tier": "load-bearing", "consumers": found,
            }
        for declaration, origin, found in examples_only:
            payload["declarations"][declaration] = {
                "origin": origin, "tier": "examples-only", "consumers": found,
            }
            payload["work_queue"].append(declaration)
        for declaration, origin in unused:
            payload["declarations"][declaration] = {
                "origin": origin, "tier": "no-consumer", "consumers": [],
            }
            payload["work_queue"].append(declaration)
        out = Path(args.json)
        out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {out} — {len(payload['declarations'])} declarations, "
              f"{len(payload['work_queue'])} in the work queue")
        return

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
