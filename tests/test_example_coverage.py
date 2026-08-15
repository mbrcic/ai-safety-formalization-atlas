"""The example-coverage gate must fail on the defect it was written for.

A gate that never fires is indistinguishable from no gate, and this one was
added *after* five uninhabited layers had already shipped — so the thing worth
asserting is not that the tree passes today but that an uninhabited module makes
it fail tomorrow.

The fixtures are minimal Lean-shaped trees rather than copies of the repository,
so a change to the real tree cannot quietly turn these into vacuous tests.

Run: `python3 -m pytest tests/ -q`
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from check_example_coverage import check  # noqa: E402


def _tree(root: Path, files: dict[str, str]) -> Path:
    for name, text in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
    return root


def test_covered_module_passes(tmp_path: Path) -> None:
    root = _tree(
        tmp_path,
        {
            "AISafetyAtlas/Widget.lean": "public def widget : Nat := 0\n",
            "AISafetyAtlas/Examples/Use.lean": "theorem t : widget = 0 := rfl\n",
        },
    )
    errors, covered, checked = check(root, {})
    assert errors == []
    assert (covered, checked) == (1, 1)


def test_uninhabited_module_fails(tmp_path: Path) -> None:
    root = _tree(
        tmp_path,
        {
            "AISafetyAtlas/Widget.lean": "public def widget : Nat := 0\n",
            "AISafetyAtlas/Examples/Use.lean": "theorem t : True := trivial\n",
        },
    )
    errors, _, _ = check(root, {})
    assert len(errors) == 1
    assert "AISafetyAtlas/Widget.lean" in errors[0]
    assert "no example references any of them" in errors[0]


def test_exemption_suppresses_the_failure(tmp_path: Path) -> None:
    root = _tree(
        tmp_path,
        {
            "AISafetyAtlas/Widget.lean": "public def widget : Nat := 0\n",
            "AISafetyAtlas/Examples/Use.lean": "theorem t : True := trivial\n",
        },
    )
    errors, _, _ = check(root, {"AISafetyAtlas/Widget.lean": "reason"})
    assert errors == []


def test_stale_exemption_fails(tmp_path: Path) -> None:
    """An exemption that has gained coverage must be removed, not left to rot."""
    root = _tree(
        tmp_path,
        {
            "AISafetyAtlas/Widget.lean": "public def widget : Nat := 0\n",
            "AISafetyAtlas/Examples/Use.lean": "theorem t : widget = 0 := rfl\n",
        },
    )
    errors, _, _ = check(root, {"AISafetyAtlas/Widget.lean": "reason"})
    assert len(errors) == 1
    assert "drop its EXEMPT entry" in errors[0]


def test_exemption_of_a_missing_file_fails(tmp_path: Path) -> None:
    root = _tree(tmp_path, {"AISafetyAtlas/Examples/Use.lean": "\n"})
    errors, _, _ = check(root, {"AISafetyAtlas/Gone.lean": "reason"})
    assert len(errors) == 1
    assert "does not exist" in errors[0]


def test_exemption_without_a_reason_fails(tmp_path: Path) -> None:
    root = _tree(
        tmp_path,
        {
            "AISafetyAtlas/Widget.lean": "public def widget : Nat := 0\n",
            "AISafetyAtlas/Examples/Use.lean": "theorem t : True := trivial\n",
        },
    )
    errors, _, _ = check(root, {"AISafetyAtlas/Widget.lean": "  "})
    assert any("carries no reason" in error for error in errors)


def test_facade_without_declarations_is_not_counted(tmp_path: Path) -> None:
    root = _tree(
        tmp_path,
        {
            "AISafetyAtlas/Facade.lean": "public import AISafetyAtlas.Widget\n",
            "AISafetyAtlas/Examples/Use.lean": "\n",
        },
    )
    errors, covered, checked = check(root, {})
    assert errors == []
    assert (covered, checked) == (0, 0)


def test_qualified_reference_counts(tmp_path: Path) -> None:
    root = _tree(
        tmp_path,
        {
            "AISafetyAtlas/Widget.lean": "public def widget : Nat := 0\n",
            "AISafetyAtlas/Examples/Use.lean": "theorem t : Atlas.widget = 0 := rfl\n",
        },
    )
    errors, covered, _ = check(root, {})
    assert errors == []
    assert covered == 1
