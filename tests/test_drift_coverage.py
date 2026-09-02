"""Coverage of the drift checker, and the scope rules that decide what it owes.

``check_drift_coverage.py`` asks the elaborated environment what declarations
exist and holds ``check_statement_drift.py`` to that list. The parts worth
testing without a Lean build are the three judgement calls it encodes -- which
declarations the compiler generated, which ones no source line could have named,
and whether the drift checker's namespace tracking produces the qualified name
the environment will report -- because getting any of them wrong hides real
declarations, which is the failure the whole check exists to prevent.

Run: `python3 -m pytest tests/ -q`
"""

from __future__ import annotations

import importlib.util
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


drift = _load("check_statement_drift")
coverage = _load("check_drift_coverage")


def _keys(source: str) -> list[tuple[str, str]]:
    return [(kind, qualified) for kind, qualified, _o, _b in drift._blocks(source)]


# --- Namespace tracking: the bug this check was written to find ---------------
#
# `section` shares the `end` keyword with `namespace`. Popping one stack for both
# meant a bare `end` closing an unnamed section took the enclosing namespace with
# it, and every declaration after that point was keyed unqualified. That is a
# rename, and a rename is a removal plus an addition, so a whole file could have
# been compared against nothing.


def test_a_bare_end_closes_the_section_not_the_namespace() -> None:
    source = (
        "namespace Foo\n"
        "section\n"
        "public theorem a : True := trivial\n"
        "end\n"
        "public theorem b : True := trivial\n"
        "end Foo\n"
    )
    assert ("theorem", "Foo.b") in _keys(source)
    assert ("theorem", "b") not in _keys(source)


def test_a_named_end_closes_its_own_scope() -> None:
    source = (
        "namespace Foo\n"
        "section Bar\n"
        "public theorem a : True := trivial\n"
        "end Bar\n"
        "public theorem b : True := trivial\n"
        "end Foo\n"
    )
    assert ("theorem", "Foo.a") in _keys(source)
    assert ("theorem", "Foo.b") in _keys(source)


def test_nested_namespaces_unwind_one_at_a_time() -> None:
    source = (
        "namespace A\n"
        "namespace B\n"
        "public theorem x : True := trivial\n"
        "end B\n"
        "public theorem y : True := trivial\n"
        "end A\n"
    )
    assert ("theorem", "A.B.x") in _keys(source)
    assert ("theorem", "A.y") in _keys(source)


def test_a_section_is_still_reported() -> None:
    """It scopes `variable`, so dropping it from the report would lose meaning."""
    source = "namespace Foo\nsection\npublic theorem a : True := trivial\nend\nend Foo\n"
    assert any(kind == "section" for kind, _ in _keys(source))


def test_leaving_a_namespace_stops_qualifying() -> None:
    source = (
        "namespace Foo\n"
        "public theorem a : True := trivial\n"
        "end Foo\n"
        "public theorem c : True := trivial\n"
    )
    assert ("theorem", "Foo.a") in _keys(source)
    assert ("theorem", "c") in _keys(source)


# --- What counts as compiler-generated ---------------------------------------


def _row(name: str, kind: str, start: str, stop: str, module: str = "M") -> dict:
    return {
        "name": name,
        "kind": kind,
        "module": module,
        "generated": False,
        "range": start,
        "end": stop,
        "instance": False,
    }


def test_a_declaration_starting_inside_another_is_generated() -> None:
    """`deriving DecidableEq` points back into the inductive's own span."""
    rows = [
        _row("M.CandIx", "inductive", "189:0", "195:24"),
        _row("M.instDecidableEqCandIx", "def", "194:11", "194:22"),
    ]
    coverage.mark_contained(rows)
    assert rows[0]["generated"] is False, "the type itself is hand-written"
    assert rows[1]["generated"] is True, "the derived instance is not"


def test_a_top_level_declaration_is_not_generated() -> None:
    """The case that must survive: a hand-written instance below the type."""
    rows = [
        _row("M.CandIx", "inductive", "189:0", "195:24"),
        _row("M.instFintypeCandIx", "def", "201:0", "204:10"),
    ]
    coverage.mark_contained(rows)
    assert rows[1]["generated"] is False


def test_ext_theorems_sharing_a_structures_span_are_generated() -> None:
    rows = [
        _row("M.PairModel", "inductive", "60:0", "75:0"),
        _row("M.PairModel.ext", "theorem", "71:2", "71:9"),
        _row("M.PairModel.ext_iff", "theorem", "71:2", "71:9"),
    ]
    coverage.mark_contained(rows)
    assert [r["generated"] for r in rows] == [False, True, True]


def test_adjacent_declarations_do_not_contain_each_other() -> None:
    rows = [_row("M.f", "def", "10:0", "12:0"), _row("M.g", "def", "12:0", "14:0")]
    coverage.mark_contained(rows)
    assert [r["generated"] for r in rows] == [False, False]


def test_containment_does_not_cross_modules() -> None:
    rows = [
        _row("A.big", "def", "1:0", "999:0", module="A"),
        _row("B.small", "def", "5:0", "6:0", module="B"),
    ]
    coverage.mark_contained(rows)
    assert rows[1]["generated"] is False


# --- Names no source line could have written ---------------------------------


def test_a_notation_constant_is_unnameable() -> None:
    """Lean escapes it precisely because it is not a legal identifier."""
    assert coverage.unnameable("AISafetyAtlas.Upstream.Arrow.«term_≻[_]_»")


def test_an_ordinary_declaration_is_nameable() -> None:
    assert not coverage.unnameable("AISafetyAtlas.Causal.Model.ext")


def test_notation_commands_count_as_unnamed_units() -> None:
    """The drift checker keys a `notation` by its first parameter, not a name.

    So the environment's `«term_...»` and the checker's `Arrow.a` describe the
    same command and can only be reconciled by counting.
    """
    source = (
        "namespace Arrow\n"
        'notation a " ≻[" p "] " b => Preorder\'.lt p b a\n'
        'notation a " ≽[" p "] " b => Preorder\'.le p b a\n'
        "end Arrow\n"
    )
    counted = sum(
        1 for kind, _q, _o, _b in drift._blocks(source)
        if kind in coverage.UNNAMED_COMMAND_KINDS
    )
    assert counted == 2


def test_private_names_are_unmangled() -> None:
    """`_private.M.0.helper` is written `helper`, which is what the checker keys."""
    row = {"name": "_private.AISafetyAtlas.Upstream.Debate.Cost.0.verabind_cost_eq_zero"}
    assert coverage.source_name(row) == "verabind_cost_eq_zero"


def test_a_public_name_is_left_alone() -> None:
    row = {"name": "AISafetyAtlas.Causal.Model.ext"}
    assert coverage.source_name(row) == "AISafetyAtlas.Causal.Model.ext"


def test_every_exclusion_carries_a_reason() -> None:
    for name, reason in coverage.load_exclusions().items():
        assert reason.strip(), f"{name} is excluded with no reason"


def _fake_tree(root: Path, sources: list[str], oleans: list[str]) -> None:
    """A tree where the set of sources and the set of artifacts can disagree."""
    build = root / ".lake" / "build" / "lib" / "lean"
    for name in sources:
        path = root / (name.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("-- source\n", encoding="utf-8")
    for name in oleans:
        path = build / (name.replace(".", "/") + ".olean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"olean")


def test_an_olean_whose_source_is_gone_is_not_a_module(tmp_path: Path) -> None:
    """The failure this guards: lake leaves build output behind when a source is
    renamed away, a restored cache carries the orphan onto a fresh runner, and
    importing it fails with "incompatible header" -- which reads as a broken
    tree rather than as a stale artifact."""
    _fake_tree(
        tmp_path,
        sources=["AISafetyAtlas", "AISafetyAtlas.Live"],
        oleans=["AISafetyAtlas", "AISafetyAtlas.Live", "AISafetyAtlas.Causal.Gone"],
    )
    assert coverage.built_modules(tmp_path) == ["AISafetyAtlas", "AISafetyAtlas.Live"]


def test_a_source_outside_every_target_is_still_not_a_module(tmp_path: Path) -> None:
    """The other half, and the reason discovery is artifact-based to begin with:
    a `.lean` that no target builds must not become an import error."""
    _fake_tree(
        tmp_path,
        sources=["AISafetyAtlas", "AISafetyAtlas.Live", "AISafetyAtlas.Unbuilt"],
        oleans=["AISafetyAtlas", "AISafetyAtlas.Live"],
    )
    assert coverage.built_modules(tmp_path) == ["AISafetyAtlas", "AISafetyAtlas.Live"]
