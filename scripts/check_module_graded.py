#!/usr/bin/env python3
"""Every library module is named in a ledger, or is excluded with a reason.

The hole this closes: a cluster of new public Lean can land with **zero rows in
`registry.yaml`** and no section in the coverage audit, and the gate returns 0 --
not despite the rows being absent, but *because* they are. Nothing mapped a
module to a ledger entry, so "nobody graded this" and "this needs no grading"
were indistinguishable, and fourteen modules of the 2026-09-10 merge sat in
exactly that state until a review found them by hand.

A module counts as named when `registry.yaml`, `conjectures.yaml` or
`docs/provenance/source-coverage-audit.md` mentions its dotted module path, **or
names one of the declarations the build says that module defines**. The second
form is the usual one, because the ledgers write declarations rather than module
paths -- `ProgramPrior.expectation_eq_programSum`, never
`AISafetyAtlas.Wireheading.ProgramPrior`.

**The declaration is looked up in `docs/status/declaration-index.json`, not
guessed from the module's name, and the first version of this check guessed.** It
accepted a module's final component occurring anywhere in ledger prose, so
`Decision.Expect` and `Sovereignty.Boundary` passed on the ordinary English words
"Expect" and "Boundary" while a review found both genuinely uncited. Tightening
that to a namespace-shaped `Tail.` mention does not fix it either, and the reason
is structural: **a declaration's namespace is not its module.**
`AISafetyAtlas.Conjectures.MAIS.O26` defines `maisO26_exactRate` in namespace
`AISafetyAtlas.Conjectures.MAIS`, so no spelling of that declaration contains the
word `O26` as a namespace, and seventeen modules that *are* cited would have been
reported as silent. The index is the only thing that knows which module a name
came from, which is the same reason `check_witness_debt` reads it.

A mention that is a dotted suffix of more than one declaration is **refused**, the
way `check_witness_debt` refuses an ambiguous bare leaf: it is evidence for every
declaration carrying that suffix and therefore for none of them. An exact full
name always resolves, whatever else shares its leaf.

All of this is still deliberately loose about *quality*. The point is not to grade
a module here, it is to make total silence about one impossible to reach by
accident.

Everything else must carry a line in the exclusions file, and the line must say
why. Most legitimate exclusions are support layers -- machinery beneath a module
that *is* graded, carrying no printed statement of their own -- and saying so
costs one line. `UNREVIEWED` is a permitted reason and is itself the worklist:
it records that a module was inherited when this check was introduced and that
nobody has yet decided which of the two cases it is. An unreviewed entry is not
a defect; having no entry is, because that is the state this check exists to
make unreachable.

Stale exclusions fail too. An entry naming a module the tree no longer has is a
silent licence for some future module to inherit its name.

Usage:
    python3 scripts/check_module_graded.py
    python3 scripts/check_module_graded.py --write   # seed or refresh entries
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
INDEX = ROOT / "docs" / "status" / "declaration-index.json"
EXCLUSIONS = ROOT / "docs" / "status" / "module-grading-exclusions.json"

LEDGERS = (
    "registry.yaml",
    "conjectures.yaml",
    "docs/provenance/source-coverage-audit.md",
)

# Worked witnesses and vendored third-party code carry no atlas grading
# obligation: the first are evidence about library modules, the second are
# somebody else's results under a pinned revision.
SKIP_PREFIXES = ("AISafetyAtlas.Examples", "AISafetyAtlas.Upstream")

UNREVIEWED = "UNREVIEWED"


def declarations_by_module() -> dict[str, set[str]]:
    """module -> the declarations the build says it defines.

    `kind == "module"` entries are the modules themselves and carry no
    declaration, so they are dropped.
    """
    index = json.loads(INDEX.read_text(encoding="utf-8"))
    homes: dict[str, set[str]] = {}
    for declaration in index["declarations"]:
        module = declaration.get("module", "")
        if not module.startswith("AISafetyAtlas"):
            continue
        # A `module` entry is the module itself. It contributes no name, but the
        # module still has to appear in the list: a facade that defines nothing
        # cannot be graded by declaration and therefore needs an exclusion, which
        # is precisely the case this check exists to make visible.
        homes.setdefault(module, set())
        if declaration.get("kind") != "module":
            homes[module].add(declaration["name"])
    return homes


def library_modules(homes: dict[str, set[str]]) -> list[str]:
    return sorted(
        module
        for module in homes
        if module != "AISafetyAtlas" and not module.startswith(SKIP_PREFIXES)
    )


def ledger_text() -> str:
    return "\n".join((ROOT / name).read_text(encoding="utf-8") for name in LEDGERS)


BACKTICK = re.compile(r"`([^`]+)`")
STRUCTURED = ("registry.yaml", "conjectures.yaml")


def scalars(node: object) -> list[str]:
    """Every string scalar in a parsed ledger, at any depth."""
    if isinstance(node, str):
        return [node]
    if isinstance(node, dict):
        return [item for value in node.values() for item in scalars(value)]
    if isinstance(node, list):
        return [item for value in node for item in scalars(value)]
    return []


def ledger_runs() -> set[str]:
    """Identifier runs the ledgers offer **as names**, not as English.

    Two sources, and neither is bare prose. Structured scalars with no
    whitespace are the declaration-carrying fields -- `lean`,
    `atlas_declaration`, the `declarations` lists -- separated from the notes
    around them by the fact that prose contains spaces. Backticked spans are how
    a note names a declaration in the middle of a sentence.

    Bare prose is excluded on purpose. `expect` and `reach` are ordinary English
    words *and* leaf names in this tree, and accepting them unquoted is how the
    first version of this check reported two modules as graded on sentences that
    were not about them.
    """
    runs: set[str] = set()
    for name in LEDGERS:
        text = (ROOT / name).read_text(encoding="utf-8")
        for span in BACKTICK.findall(text):
            runs.update(TOKEN.findall(span))
    for name in STRUCTURED:
        payload = json.loads((ROOT / name).read_text(encoding="utf-8"))
        for scalar in scalars(payload):
            if scalar and not any(character.isspace() for character in scalar):
                runs.update(TOKEN.findall(scalar))
    return runs


TOKEN = re.compile(r"[\w'.]+")


def named_modules(homes: dict[str, set[str]], haystack: str, runs: set[str]) -> set[str]:
    """Every module a ledger mentions, by module path or by one of its names.

    A ledger run is resolved against the index: its exact full name if it has
    one, otherwise the single declaration it is a dotted suffix of. A suffix
    carried by two declarations resolves to neither.
    """
    owner: dict[str, str] = {}
    ambiguous: set[str] = set()
    for module, declarations in homes.items():
        for name in declarations:
            parts = name.split(".")
            for index in range(len(parts)):
                form = ".".join(parts[index:])
                if form in owner and owner[form] != module:
                    ambiguous.add(form)
                owner.setdefault(form, module)
    # An exact full name always wins over the ambiguity of its own leaf.
    exact = {name: module for module, names in homes.items() for name in names}

    found = {module for module in homes if module in haystack}
    for run in runs:
        if run in exact:
            found.add(exact[run])
        elif run in owner and run not in ambiguous:
            found.add(owner[run])
    return found


def load_exclusions() -> dict[str, str]:
    if not EXCLUSIONS.exists():
        return {}
    data = json.loads(EXCLUSIONS.read_text(encoding="utf-8"))
    return dict(data.get("modules", {}))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write",
        action="store_true",
        help="add missing modules as UNREVIEWED and drop stale entries",
    )
    arguments = parser.parse_args()

    homes = declarations_by_module()
    modules = library_modules(homes)
    haystack = ledger_text()
    mentioned = named_modules(homes, haystack, ledger_runs())
    graded = {module for module in modules if module in mentioned}
    ungraded = [module for module in modules if module not in graded]
    exclusions = load_exclusions()

    if arguments.write:
        kept = {
            module: reason
            for module, reason in exclusions.items()
            if module in ungraded
        }
        for module in ungraded:
            kept.setdefault(module, UNREVIEWED)
        EXCLUSIONS.write_text(
            json.dumps(
                {
                    "note": (
                        "Library modules named in no ledger, each with the reason "
                        "it needs none. Written by scripts/check_module_graded.py "
                        "--write; reasons are edited by hand. UNREVIEWED means the "
                        "module was inherited when the check was introduced and "
                        "nobody has yet decided whether it is a support layer or a "
                        "missing row."
                    ),
                    "modules": dict(sorted(kept.items())),
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
        print(f"module grading exclusions written: {len(kept)} -> {EXCLUSIONS}")
        return 0

    problems: list[str] = []
    for module in ungraded:
        if module not in exclusions:
            problems.append(
                f"{module} is named in no ledger and has no exclusion entry"
            )
        elif not str(exclusions[module]).strip():
            problems.append(f"{module} has an empty exclusion reason")
    for module in sorted(set(exclusions) - set(ungraded)):
        problems.append(
            f"{module} carries an exclusion but is graded or no longer exists"
        )

    if problems:
        for problem in problems:
            print(f"check_module_graded: {problem}", file=sys.stderr)
        print(
            "check_module_graded: add a ledger row, or record the reason with "
            "--write and then replace UNREVIEWED with it",
            file=sys.stderr,
        )
        return 1

    unreviewed = sum(1 for reason in exclusions.values() if reason == UNREVIEWED)
    print(
        f"check_module_graded ok: {len(modules)} library modules, "
        f"{len(graded)} named in a ledger, {len(exclusions)} excluded with a "
        f"reason ({unreviewed} still {UNREVIEWED})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
