"""The citation checker's identifier alphabet is Lean's, not ASCII.

`check_cited_declarations` reads grading artifacts and reports any Lean name
they cite that the elaborated index does not carry. Its tokenizer was ASCII
plus the two characters somebody happened to need, which meant a correctly
cited declaration containing any other Unicode letter would be truncated and
then reported as missing.

`AISafetyAtlas.Fairness.sum_score_eq_μ` is the in-tree proof that this is not
hypothetical. The defect was latent rather than live -- no scanned artifact
cites that theorem today -- which is precisely why it would otherwise have been
found by someone writing a correct citation and being told it was wrong.

The trailing-quote case is guarded here too, because it is the one this
script's own header records as its first bug, and widening the alphabet is an
easy way to reintroduce it: `'` must stay *outside* the tail class and be
matched only by the trailing anchor, or the tokenizer eats the possessive in
prose like "boltzmann_minimax_floor's premise".
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "check_cited_declarations.py"


def _module():
    spec = importlib.util.spec_from_file_location("check_cited_declarations", SCRIPT)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


TOKEN = _module().TOKEN


@pytest.mark.parametrize(
    "text, expected",
    [
        ("sum_score_eq_μ", "sum_score_eq_μ"),
        ("boltzmannTrueProbability_eq_of_Δmask", "boltzmannTrueProbability_eq_of_Δmask"),
        ("Δ_fixProfile", "Δ_fixProfile"),
        ("accuracySupOn_eq_sup'", "accuracySupOn_eq_sup'"),
        ("behaviorEq_of_child_eq_zero", "behaviorEq_of_child_eq_zero"),
    ],
)
def test_a_real_declaration_name_is_tokenized_whole(text: str, expected: str) -> None:
    assert TOKEN.findall(text) == [expected]


def test_a_possessive_does_not_extend_the_token() -> None:
    """`'` belongs to the trailing anchor, never to the tail class."""
    (found,) = TOKEN.findall("boltzmann_minimax_floor's premise")
    assert not found.endswith("s")


def test_print_notation_is_still_matched_and_filtered_elsewhere() -> None:
    """Widening the alphabet must not change what reaches the vocabulary filters."""
    assert TOKEN.findall("C_j") == ["C_j"]
