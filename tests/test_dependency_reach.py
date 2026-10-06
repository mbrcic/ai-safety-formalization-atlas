"""Which dependency moves are scoped, and what a scoped drift check still sees.

``dependency_reach.py`` decides how much of the environment the drift check
elaborates when a dependency moves. A wrong decision in one direction costs time;
in the other it hides a statement whose meaning changed. These tests pin the
second direction: every move that could reach Mathlib stays whole, a module
reached only through another atlas module or another package stays in scope, and
a scoped comparison still fails on a silent change inside its scope.
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))


def _load(name: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / f"{name}.py")
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


reach = _load("dependency_reach")
drift = _load("check_elaboration_drift")


def _manifest(**revs: tuple[str, bool]) -> str:
    return json.dumps(
        {"packages": [{"name": name, "rev": rev, "inherited": inherited} for name, (rev, inherited) in revs.items()]}
    )


LAKEFILE = '[[lean_lib]]\nname = "AISafetyAtlas"\n'


def _classify(changed: list[str], base: str, head: str, base_lake: str = LAKEFILE, head_lake: str = LAKEFILE):
    return reach.classify_move(changed, base, head, base_lake, head_lake)


# --- The decision ------------------------------------------------------------


def test_a_directly_required_package_moving_is_scoped() -> None:
    base = _manifest(mathlib=("m1", False), Causalean=("c1", False))
    head = _manifest(mathlib=("m1", False), Causalean=("c2", False))
    kind, moved, _ = _classify(["lake-manifest.json"], base, head)
    assert (kind, moved) == ("scoped", ["Causalean"])


def test_mathlib_moving_is_whole() -> None:
    base = _manifest(mathlib=("m1", False))
    head = _manifest(mathlib=("m2", False))
    assert _classify(["lake-manifest.json"], base, head)[0] == "whole"


def test_an_inherited_package_moving_is_whole() -> None:
    """It arrives through Mathlib, Foundation or PFR; its reach is not ours to scope."""
    base = _manifest(Causalean=("c1", False), batteries=("b1", True))
    head = _manifest(Causalean=("c2", False), batteries=("b2", True))
    assert _classify(["lake-manifest.json"], base, head)[0] == "whole"


def test_the_toolchain_or_a_baseline_moving_is_whole() -> None:
    same = _manifest(mathlib=("m1", False))
    assert _classify(["lean-toolchain"], same, same)[0] == "whole"
    assert _classify(["docs/status/elab-baseline-v4330.json"], same, same)[0] == "whole"


def test_lean_options_moving_is_whole() -> None:
    same = _manifest(mathlib=("m1", False))
    changed = LAKEFILE + "leanOptions = { autoImplicit = false }\n"
    assert _classify(["lakefile.toml"], same, same, LAKEFILE, changed)[0] == "whole"


def test_adding_a_package_is_no_move() -> None:
    base = _manifest(mathlib=("m1", False))
    head = _manifest(mathlib=("m1", False), Causalean=("c1", False))
    assert _classify(["lake-manifest.json", "lakefile.toml"], base, head)[0] == "none"


# --- The reach ---------------------------------------------------------------


def _tree(root: Path, modules: dict[str, str], packages: dict[str, dict]) -> list[str]:
    """Atlas sources by module name, and fetched packages: name -> {roots, requires}."""
    for module, source in modules.items():
        path = root / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
    for package, spec in packages.items():
        directory = root / ".lake" / "packages" / package
        directory.mkdir(parents=True, exist_ok=True)
        for module_root in spec.get("roots", []):
            (directory / f"{module_root}.lean").write_text("", encoding="utf-8")
        (directory / "lake-manifest.json").write_text(
            json.dumps({"packages": [{"name": name} for name in spec.get("requires", [])]}),
            encoding="utf-8",
        )
    return list(modules)


def test_reach_follows_atlas_imports_and_drops_the_rest(tmp_path: Path) -> None:
    modules = _tree(
        tmp_path,
        {
            "AISafetyAtlas.Causal.DSep": "module\npublic import Causalean.Graph.DSep.Separation\n",
            "AISafetyAtlas.Causal.Requisite": "module\npublic import AISafetyAtlas.Causal.DSep\n",
            "AISafetyAtlas.Other": "module\npublic import Mathlib.Data.Fin.Basic\n",
        },
        {"Causalean": {"roots": ["Causalean"], "requires": ["mathlib"]}, "mathlib": {"roots": ["Mathlib"]}},
    )
    scoped, _ = reach.reach(["Causalean"], modules, root=tmp_path)
    assert scoped == ["AISafetyAtlas.Causal.DSep", "AISafetyAtlas.Causal.Requisite"]


def test_reach_follows_a_package_that_requires_the_moved_one(tmp_path: Path) -> None:
    """A module importing only Q is still reached when Q's manifest lists P."""
    modules = _tree(
        tmp_path,
        {"AISafetyAtlas.UsesQ": "import Q.Thing\n", "AISafetyAtlas.Plain": "import Mathlib\n"},
        {"P": {"roots": ["P"]}, "Q": {"roots": ["Q"], "requires": ["P"]}, "mathlib": {"roots": ["Mathlib"]}},
    )
    scoped, _ = reach.reach(["P"], modules, root=tmp_path)
    assert scoped == ["AISafetyAtlas.UsesQ"]


def test_a_move_carried_by_mathlib_is_whole(tmp_path: Path) -> None:
    modules = _tree(
        tmp_path,
        {"AISafetyAtlas.Plain": "import Mathlib\n"},
        {"P": {"roots": ["P"]}, "mathlib": {"roots": ["Mathlib"], "requires": ["P"]}},
    )
    scoped, reason = reach.reach(["P"], modules, root=tmp_path)
    assert scoped is None
    assert "Mathlib" in reason


def test_an_unfetched_package_is_whole(tmp_path: Path) -> None:
    modules = _tree(tmp_path, {"AISafetyAtlas.Plain": "import Mathlib\n"}, {})
    assert reach.reach(["P"], modules, root=tmp_path)[0] is None


# --- The scoped comparison ---------------------------------------------------


def _decl(fp: str, pp: str, module: str) -> dict:
    return {"kind": "theorem", "module": module, "generated": False, "fp": fp, "pp": pp}


def _dump(path: Path, decls: dict, scope: dict | None = None) -> Path:
    payload = {
        "toolchain": "leanprover/lean4:v4.33.0",
        "commit": "0" * 40,
        "modules": 1,
        "selector": "module",
        "raw": True,
        "declarations": decls,
    }
    if scope is not None:
        payload["scope"] = scope
    drift.write_dump(path, payload)
    return path


def test_a_scoped_comparison_ignores_modules_outside_the_scope(tmp_path: Path) -> None:
    """Declarations it never elaborated are neither removed nor compared."""
    old = _dump(
        tmp_path / "old.json",
        {"A.inScope": _decl("a", "P", "M.In"), "B.outside": _decl("b", "Q", "M.Out")},
    )
    new = _dump(
        tmp_path / "new.json",
        {"A.inScope": _decl("a", "P", "M.In")},
        {"packages": ["Causalean"], "modules": ["M.In"]},
    )
    assert drift.do_compare(old, new, 0, "silent") == 0


def test_a_scoped_comparison_still_fails_a_silent_change_inside_it(tmp_path: Path) -> None:
    old = _dump(tmp_path / "old.json", {"A.inScope": _decl("a", "P", "M.In")})
    new = _dump(
        tmp_path / "new.json",
        {"A.inScope": _decl("z", "P", "M.In")},
        {"packages": ["Causalean"], "modules": ["M.In"]},
    )
    assert drift.do_compare(old, new, 0, "silent") == 1


def test_a_scope_no_module_reaches_passes_and_says_so(tmp_path: Path, capsys) -> None:
    old = _dump(tmp_path / "old.json", {"B.outside": _decl("b", "Q", "M.Out")})
    new = _dump(tmp_path / "new.json", {}, {"packages": ["Unused"], "modules": []})
    assert drift.do_compare(old, new, 0, "silent") == 0
    assert "no atlas module imports the moved package" in capsys.readouterr().out


def test_a_comment_edit_in_the_lakefile_is_no_move() -> None:
    """The repin itself edits a comment beside the options; that must stay scoped."""
    same = _manifest(mathlib=("m1", False))
    base = "[leanOptions]\nautoImplicit = false\n\n[[require]]\nname = \"Causalean\"\n"
    head = "# a new note\n" + base
    assert _classify(["lakefile.toml"], same, same, base, head)[0] == "none"


def test_a_multi_line_option_value_is_read_whole() -> None:
    same = _manifest(mathlib=("m1", False))
    base = '[[lean_lib]]\nname = "A"\nmoreLeanArgs = [\n  "-DmaxHeartbeats=400000",\n]\n'
    head = base.replace("400000", "800000")
    assert _classify(["lakefile.toml"], same, same, base, head)[0] == "whole"
