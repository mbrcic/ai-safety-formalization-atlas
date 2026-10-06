#!/usr/bin/env python3
"""Which kind of dependency migration a change is, and which atlas modules it reaches.

`check_elaboration_drift.py` exists for the change where the source does not move
and its meaning does: an upstream rename behind an alias, a different instance
chosen. CI runs it when a dependency moves. Elaborating the whole environment
costs 342 s on an idle 12-core host and runs past the 30-minute budget on a
two-core hosted runner, and for most dependencies most of that is wasted. A
module's elaboration depends only on the toolchain, the Lean options and its
own import closure, so a moved package can change the meaning of a declaration
only in a module whose imports reach that package.

Two kinds of move are kept whole:

* the toolchain, the Lean options in `lakefile.toml`, or a committed baseline
  dump moving -- they reach every module;
* Mathlib, or any package this repository does not require directly (its
  manifest entry is `inherited`). Those arrive through Mathlib, Foundation or
  PFR, and Mathlib alone is imported by nearly everything here, so scoping them
  would save little and rest on a reach computation over the whole ecosystem.

Every other moved package -- one this repository requires directly, such as
Causalean -- is a scoped move: the drift check elaborates only the atlas modules
whose import closure reaches it. The reach is computed after `lake` has fetched
the packages. A package whose own manifest lists the moved one carries the move
too, and if that set includes Mathlib the move is treated as whole after all.

    python3 scripts/dependency_reach.py decide BASE HEAD
    python3 scripts/dependency_reach.py reach Causalean
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "AISafetyAtlas"
PACKAGES = ROOT / ".lake" / "packages"

# Baselines count because re-dumping one *is* the migration act; a branch that
# rewrites the baseline without re-comparing against it would gate itself out of
# the only check that reads it.
WHOLE_FILES = re.compile(r"^(lean-toolchain|docs/status/elab-baseline-.*\.json)$")
OPTION_KEYS = ("leanOptions", "moreLeanArgs", "moreServerOptions")

# Over-approximates on purpose: an `import` line inside a docstring counts as an
# import. A module wrongly kept in scope costs elaboration time; one wrongly
# dropped would hide a change.
IMPORT_RE = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z_«][\w.«»']*)",
    re.MULTILINE,
)


def _git_show(ref: str, path: str) -> str | None:
    out = subprocess.run(
        ["git", "-C", str(ROOT), "show", f"{ref}:{path}"], capture_output=True, text=True
    )
    return out.stdout if out.returncode == 0 else None


def manifest_entries(text: str | None) -> dict[str, dict]:
    if text is None:
        return {}
    return {entry["name"]: entry for entry in json.loads(text)["packages"]}


def lean_options(text: str | None) -> tuple[dict, dict] | None:
    """The Lean options a `lakefile.toml` sets, at package and at library level."""
    if text is None:
        return None
    config = tomllib.loads(text)
    libraries = {
        library.get("name"): {key: library.get(key) for key in OPTION_KEYS}
        for library in config.get("lean_lib", [])
    }
    return {key: config.get(key) for key in OPTION_KEYS}, libraries


def classify_move(
    changed_files: list[str],
    base_manifest: str | None,
    head_manifest: str | None,
    base_lakefile: str | None,
    head_lakefile: str | None,
) -> tuple[str, list[str], str]:
    """Return (kind, moved packages, reason); kind is `none`, `scoped` or `whole`.

    Adding a package is not a move: nothing already in the tree imports it.
    """
    whole_files = [name for name in changed_files if WHOLE_FILES.match(name)]
    base, head = manifest_entries(base_manifest), manifest_entries(head_manifest)
    moved = sorted(name for name in base.keys() & head.keys() if base[name].get("rev") != head[name].get("rev"))

    reasons: list[str] = []
    if whole_files:
        reasons.append("changed " + ", ".join(whole_files))
    old_options, new_options = lean_options(base_lakefile), lean_options(head_lakefile)
    if old_options and new_options:
        if old_options[0] != new_options[0]:
            reasons.append("package Lean options changed")
        reasons += [
            f"Lean options of {name} changed"
            for name in old_options[1].keys() & new_options[1].keys()
            if old_options[1][name] != new_options[1][name]
        ]
    pervasive = [name for name in moved if name == "mathlib" or head[name].get("inherited")]
    if pervasive:
        reasons.append("moved " + ", ".join(pervasive) + " (Mathlib or not required directly)")

    if reasons:
        return "whole", moved, "; ".join(reasons)
    if moved:
        return "scoped", moved, "moved " + ", ".join(moved) + " (required directly)"
    return "none", [], "no dependency moved"


def decide(base: str, head: str) -> tuple[str, list[str], str]:
    diff = subprocess.run(
        ["git", "-C", str(ROOT), "diff", "--name-only", base, head],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.split()
    return classify_move(
        diff,
        _git_show(base, "lake-manifest.json"),
        _git_show(head, "lake-manifest.json"),
        _git_show(base, "lakefile.toml"),
        _git_show(head, "lakefile.toml"),
    )


def carriers(packages_dir: Path, moved: set[str]) -> set[str]:
    """The moved packages and every fetched package whose manifest lists one of them."""
    reached = set(moved)
    manifests = {
        path.parent.name: manifest_entries(path.read_text(encoding="utf-8"))
        for path in packages_dir.glob("*/lake-manifest.json")
    }
    changed = True
    while changed:
        changed = False
        for package, entries in manifests.items():
            if package not in reached and reached & entries.keys():
                reached.add(package)
                changed = True
    return reached


def package_roots(package_dir: Path) -> set[str]:
    """Top-level module names a package provides: `X` for `X.lean` or a directory `X/`."""
    source_dirs = [package_dir]
    lakefile = package_dir / "lakefile.toml"
    if lakefile.is_file():
        # Every `srcDir` the file names, whichever target it belongs to: an extra
        # directory can only add roots, which keeps more modules in scope.
        config = tomllib.loads(lakefile.read_text(encoding="utf-8"))
        source_dirs += [
            package_dir / target["srcDir"]
            for kind in ("lean_lib", "lean_exe")
            for target in config.get(kind, [])
            if target.get("srcDir")
        ]
    roots: set[str] = set()
    for directory in source_dirs:
        if not directory.is_dir():
            continue
        for entry in directory.iterdir():
            if entry.name.startswith(".") or entry.name == ".lake":
                continue
            if entry.suffix == ".lean":
                roots.add(entry.stem)
            elif entry.is_dir() and next(entry.rglob("*.lean"), None) is not None:
                roots.add(entry.name)
    return roots


def module_source(root: Path, module: str) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def reaching_modules(root: Path, modules: list[str], package_root_names: set[str]) -> list[str]:
    """The modules among `modules` whose import closure reaches one of the package roots."""
    ours = set(modules)
    imports = {
        module: IMPORT_RE.findall(module_source(root, module).read_text(encoding="utf-8"))
        for module in modules
        if module_source(root, module).is_file()
    }
    reached = {
        module
        for module, imported in imports.items()
        if any(name.split(".")[0] in package_root_names and name not in ours for name in imported)
    }
    changed = True
    while changed:
        changed = False
        for module, imported in imports.items():
            if module not in reached and reached & set(imported):
                reached.add(module)
                changed = True
    return [module for module in modules if module in reached]


def reach(moved: list[str], modules: list[str], root: Path = ROOT) -> tuple[list[str] | None, str]:
    """Modules a scoped move reaches, or None when it turns out to reach everything."""
    packages_dir = root / ".lake" / "packages"
    carrying = carriers(packages_dir, set(moved))
    if "mathlib" in carrying:
        return None, f"the move of {', '.join(sorted(moved))} reaches Mathlib, so it is whole"
    names: set[str] = set()
    for package in carrying:
        directory = packages_dir / package
        if not directory.is_dir():
            return None, f"package {package} is not fetched, so its reach is unknown"
        names |= package_roots(directory)
    scoped = reaching_modules(root, modules, names)
    return scoped, (
        f"{', '.join(sorted(carrying))} provide {', '.join(sorted(names))}; "
        f"{len(scoped)} of {len(modules)} module(s) import it"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    decide_parser = sub.add_parser("decide", help="classify the move between two commits")
    decide_parser.add_argument("base")
    decide_parser.add_argument("head")
    reach_parser = sub.add_parser("reach", help="list the built atlas modules a scoped move reaches")
    reach_parser.add_argument("packages", help="comma-separated package names")
    arguments = parser.parse_args()

    if arguments.command == "decide":
        kind, moved, reason = decide(arguments.base, arguments.head)
        print(f"kind={kind}")
        print(f"packages={','.join(moved)}")
        print(f"reason={reason}")
        return 0

    sys.path.insert(0, str(ROOT / "scripts"))
    from check_elaboration_drift import built_modules

    moved = [name for name in arguments.packages.split(",") if name]
    scoped, reason = reach(moved, built_modules())
    print(reason)
    for module in scoped if scoped is not None else []:
        print(f"  {module}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
