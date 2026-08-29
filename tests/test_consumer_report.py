"""`report_consumers.py` must recognise how Lean is actually written.

The consumer report answers one question — does anything outside `Examples/`
depend on this declaration — and the answer drives real decisions: the work
queue in `contributor-tasks.md`, and whether a surface is retired. A false
negative there is worse than no report, because "nothing consumes this" reads as
a fact about the mathematics when it is a fact about a regex.

Lean lets a consumer name a declaration three ways: bare, fully qualified, or
relative to an enclosing namespace. The third is the idiomatic one and the one
that used to be missed — `Oversight/JointObservation/RepairBoundary.lean` writes
`Knowledge.not_knowable_comp`, which matched neither the identifier pattern (a
dot precedes the leaf) nor the fully-qualified fallback (the module prefix is
absent). Every declaration reached that way was reported unused.

The last test is the reason the naive fix is wrong. The dot in the lookbehind is
not an accident: it stops `Other.foo` counting as a use of `Mine.foo`. Any fix
has to keep that while admitting genuine suffixes of the declaration's own name.

Run: `python3 -m pytest tests/ -q`
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

_spec = importlib.util.spec_from_file_location(
    "report_consumers", ROOT / "scripts" / "report_consumers.py"
)
assert _spec and _spec.loader
report_consumers = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(report_consumers)


DECLARATION = "AISafetyAtlas.Knowledge.not_knowable_comp"
HOME = "AISafetyAtlas.Knowledge"
CONSUMER = "AISafetyAtlas.Oversight.JointObservation.RepairBoundary"

HOME_CODE = """
public theorem not_knowable_comp (g : I → K) : True := trivial
"""


def _sources(consumer_code: str) -> dict[str, tuple[Path, str]]:
    return {
        HOME: (Path("Knowledge.lean"), HOME_CODE),
        CONSUMER: (Path("RepairBoundary.lean"), consumer_code),
    }


def _visible() -> dict[str, set[str]]:
    return {HOME: {HOME}, CONSUMER: {HOME, CONSUMER}}


def _consumers(consumer_code: str) -> list[str]:
    # The report indexes definitions and mentions once per module rather than
    # searching per (declaration, module) pair; the indexes are built here from
    # the same fixture so every assertion below still tests the real matcher.
    sources = _sources(consumer_code)
    return report_consumers.consumers(
        DECLARATION,
        report_consumers.definition_index(sources),
        report_consumers.mention_index(sources),
        sources,
        _visible(),
    )


def test_namespace_relative_reference_is_a_consumer() -> None:
    """`Knowledge.not_knowable_comp` — how the atlas actually writes it."""
    assert _consumers("  Knowledge.not_knowable_comp g hnc\n") == [CONSUMER]


def test_bare_reference_is_a_consumer() -> None:
    assert _consumers("  not_knowable_comp g hnc\n") == [CONSUMER]


def test_fully_qualified_reference_is_a_consumer() -> None:
    assert _consumers(
        "  AISafetyAtlas.Knowledge.not_knowable_comp g hnc\n"
    ) == [CONSUMER]


def test_same_leaf_in_a_foreign_namespace_is_not_a_consumer() -> None:
    """`Other.not_knowable_comp` is a different declaration, not a use of ours.

    This is what the dot in the lookbehind is for. Dropping it to fix the
    namespace-relative case would make this pass silently and inflate every
    consumer count in the report.
    """
    assert _consumers("  Other.not_knowable_comp g hnc\n") == []


def test_longer_identifier_is_not_a_consumer() -> None:
    """Substring matching would count `not_knowable_comp_aux` as a use."""
    assert _consumers("  Knowledge.not_knowable_comp_aux g hnc\n") == []


def test_fully_qualified_longer_identifier_is_not_a_consumer() -> None:
    """The mirror defect: a raw `declaration in code` substring test.

    `AISafetyAtlas.Knowledge.not_knowable_comp_aux` contains the declaration's
    full name as a prefix, so a substring fallback reports a use that is not
    there. False negatives hide work; false positives retire surfaces that were
    never consumed. Both matter.
    """
    assert _consumers(
        "  AISafetyAtlas.Knowledge.not_knowable_comp_aux g hnc\n"
    ) == []
