"""The elaboration diff, tested where a person cannot check it by reading.

``check_elaboration_drift.py`` splits into two halves with very different failure
modes. The Lean half -- the normalizer -- is validated by ``--self-test``, which
needs a toolchain and so cannot live here; the cases it decides (binder names are
noise, binder kinds are not, a different instance is a different statement) are
known-answer and are checked against a real elaborator.

This file tests the other half: the sorting of a fingerprint difference into what
a reviewer should do about it. That half is where a mistake is invisible, because
its output is a count, and a checker that reports "0 silent changes" because it
put them in the wrong bucket reads exactly like a clean migration.

So the tests below are about *misclassification*, not about crashes. Each builds
a pair of dumps in which one declaration moved in one specific way, and asserts
it lands in the bucket a reviewer would want it in.

Run: `python3 -m pytest tests/ -q`
"""

from __future__ import annotations

import importlib.util
import subprocess
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


drift = _load("check_elaboration_drift")


divergence_of = drift.divergence


def _decl(fp: str, pp: str, *, kind: str = "theorem", generated: bool = False) -> dict:
    return {"kind": kind, "module": "AISafetyAtlas.X", "generated": generated, "fp": fp, "pp": pp}


# --- The case the whole script exists for -----------------------------------


def test_an_identical_printed_type_with_a_changed_fingerprint_is_silent() -> None:
    """Source text unchanged, printed type unchanged, meaning changed.

    Invisible to the statement drift checker, to `axiom-audit`, and to a build.
    If this lands anywhere but `silent`, the script has no reason to exist.
    """
    old = {"T.foo": _decl("aaaa", "Fintype.card T = 2")}
    new = {"T.foo": _decl("bbbb", "Fintype.card T = 2")}
    assert drift.classify(old, new)["silent"] == ["T.foo"]


def test_a_silent_change_is_not_written_off_as_generated() -> None:
    """A hand-written theorem stays hand-written even when its neighbours are not."""
    old = {"T.foo": _decl("aaaa", "P", generated=False)}
    new = {"T.foo": _decl("bbbb", "P", generated=True)}
    assert drift.classify(old, new)["silent"] == ["T.foo"]
    assert drift.classify(old, new)["generated"] == []


def test_a_changed_declaration_is_never_dropped_entirely() -> None:
    """Every fingerprint difference lands in exactly one bucket, whatever it is."""
    for kind in ("theorem", "def", "inductive", "constructor", "recursor", "axiom"):
        old = {"T.foo": _decl("aaaa", "P", kind=kind)}
        new = {"T.foo": _decl("bbbb", "Q", kind=kind)}
        buckets = drift.classify(old, new)
        landed = [b for b in ("silent", "visible", "generated") if buckets[b]]
        assert landed, f"a changed {kind} was reported nowhere"
        assert len(landed) == 1, f"a changed {kind} was double-counted in {landed}"


# --- Must not cry wolf ------------------------------------------------------


def test_an_unchanged_tree_compares_clean() -> None:
    """Every bucket empty and exit 0, or the check is noise on every run."""
    same = {"T.foo": _decl("aaaa", "P"), "T.bar": _decl("cccc", "Q")}
    buckets = drift.classify(same, dict(same))
    assert all(not names for names in buckets.values())


def test_structural_declarations_are_expected_to_move() -> None:
    """Recursors and constructors encode the toolchain's choices, not ours."""
    old = {"T.rec": _decl("aaaa", "P", kind="recursor", generated=True)}
    new = {"T.rec": _decl("bbbb", "Q", kind="recursor", generated=True)}
    assert drift.classify(old, new)["generated"] == ["T.rec"]
    assert drift.classify(old, new)["visible"] == []


# --- Saying what moved, not only that something did -------------------------


def test_a_divergence_points_at_the_first_difference() -> None:
    """A reviewer holding a name and no reason cannot adjudicate anything."""
    before = "(F d (c Membership.mem []) (c A []))"
    after = "(F d (c Membership.mem []) (c B []))"
    where = divergence_of(before, after)
    assert where is not None
    assert "c A" in where and "c B" in where


def test_identical_normal_forms_have_no_divergence() -> None:
    assert divergence_of("(c X [])", "(c X [])") is None


def test_a_divergence_is_found_when_one_form_is_a_prefix_of_the_other() -> None:
    """Appended structure has no differing character position to point at."""
    assert divergence_of("(c X [])", "(c X []) (c Y [])") is not None


# --- Bookkeeping ------------------------------------------------------------


def test_appearing_and_vanishing_declarations_are_reported() -> None:
    old = {"T.gone": _decl("aaaa", "P")}
    new = {"T.new": _decl("bbbb", "Q")}
    buckets = drift.classify(old, new)
    assert buckets["removed"] == ["T.gone"]
    assert buckets["added"] == ["T.new"]


def test_a_vanished_derived_lemma_is_not_reported_as_a_lost_theorem() -> None:
    """`deriving` output lives in our namespace but is not ours to keep."""
    old = {"T.enumList": _decl("aaaa", "P", generated=True), "T.thm": _decl("cccc", "R")}
    new: dict[str, dict] = {}
    buckets = drift.classify(old, new)
    assert buckets["removed"] == ["T.thm"]
    assert buckets["removed_generated"] == ["T.enumList"]


def test_private_names_compare_by_their_source_name() -> None:
    """The digit in `_private.M.0.helper` is a build detail and must not be a diff."""
    assert drift.source_name("_private.AISafetyAtlas.X.0.helper") == "helper"
    assert drift.source_name("_private.AISafetyAtlas.X.7.helper") == "helper"
    assert drift.source_name("AISafetyAtlas.X.helper") == "AISafetyAtlas.X.helper"


def test_declarations_are_selected_by_module_and_not_by_name() -> None:
    """Vendored code lives in our modules under someone else's namespace.

    Selecting on the `AISafetyAtlas` name prefix skipped 636 declarations,
    including `Kolmogorov.FormalSystem.chaitinIncompleteness`, which a graded
    theorem in `AISafetyAtlas.Logic` is assigned from. We compile them and we
    ship them, so a silent change in one reaches our statements.
    """
    source = drift.harness_source(["AISafetyAtlas.Upstream.KolmogorovMathlib.Complexity"])
    assert 'unless m.startsWith "AISafetyAtlas."' in source
    assert "isPrefixOf n" not in source


# --- Keeping the cost of the next migration flat ----------------------------


def test_a_dump_round_trips(tmp_path: Path) -> None:
    payload = {"toolchain": "x", "raw": True, "declarations": {"T.foo": _decl("aaaa", "P")}}
    path = tmp_path / "dump.json"
    drift.write_dump(path, payload)
    assert drift.read_dump(path) == payload


def test_a_dump_is_committed_as_plain_text(tmp_path: Path) -> None:
    """Not gzipped, however much smaller that looks in the working tree.

    Git zlib-compresses every blob and deltas each dump against the one before
    it. Handing it a `.gz` defeats both: this pair measured 734,042 bytes packed
    gzipped against 391,190 as text, a cost the repository pays once per
    migration forever. The 42,000-line diff compression was reaching for is what
    `.gitattributes -diff` is for.
    """
    path = tmp_path / "dump.json"
    drift.write_dump(path, {"toolchain": "x", "raw": True, "declarations": {}})
    assert path.read_bytes()[:2] != b"\x1f\x8b"
    assert not list((ROOT / "docs" / "status").glob("elab-baseline-*.gz"))
    attributes = (ROOT / ".gitattributes").read_text(encoding="utf-8")
    assert "docs/status/elab-baseline-*.json -diff" in attributes


def test_the_committed_dumps_can_answer_classify() -> None:
    """The recorded class breakdown must be re-derivable from this repository.

    `--classify` is the whole reason a migration costs a reading of upstream's
    churn rather than a reading of every declaration it touched, and it needs
    the normal form itself. Dumps committed hashed would leave the headline
    result -- 171 silent changes, eleven classes, zero rearrangements -- as an
    assertion in a JSON file that nothing in the tree could check.
    """
    dumps = sorted((ROOT / "docs" / "status").glob("elab-baseline-*.json"))
    assert dumps, "the two sides of the last migration are the tool's only input"
    for dump in dumps:
        # The metadata sorts after the 10 MB `declarations` key, and parsing two
        # dumps to read six fields would cost more than the rest of this file.
        with dump.open("rb") as handle:
            handle.seek(-512, 2)
            tail = handle.read().decode("utf-8")
        assert '"raw": true' in tail, f"{dump.name} is hashed; --classify cannot read it"
        assert '"selector": "module"' in tail, dump.name


def _classes() -> dict[str, dict]:
    registry = drift.json.loads(drift.CLASSES_PATH.read_text(encoding="utf-8"))
    return {entry["key"]: entry for entry in registry["classes"]}


def _accounted(gone: set[str], came: set[str]) -> bool:
    """What `--classify` treats as a clean declaration."""
    fired, left_gone, left_came = drift.account(gone, came, _classes())
    return bool(fired) and not left_gone and not left_came


def test_a_recorded_class_accounts_for_its_substitution() -> None:
    """The point of the registry: a class ruled on once is never asked again."""
    gone, came = drift.substitution("(c setOf []) (c A [])", "(c Set.ofPred []) (c A [])")
    assert gone == {"setOf"} and came == {"Set.ofPred"}
    assert _accounted(gone, came)


# --- The classifier must not certify what it has not adjudicated -------------
#
# `any known constant left` looks like a class match and is not one: a class is
# a claim about a *replacement*. Under that weaker rule all three cases below
# certify clean, and all three are drift.


def test_a_known_departure_does_not_excuse_an_unknown_arrival() -> None:
    """`setOf -> Evil` is not the `setOf` class, whatever left."""
    assert not _accounted({"setOf"}, {"Evil"})


def test_an_unrelated_substitution_cannot_ride_along() -> None:
    """A real class in the same statement must not launder a second change."""
    assert not _accounted({"setOf", "Foo"}, {"Set.ofPred", "Bar"})


def test_an_extra_arrival_is_not_swallowed() -> None:
    """The adjudicated replacement happened *and* something else arrived."""
    assert not _accounted({"setOf"}, {"Set.ofPred", "Sneaky"})


def test_every_class_states_its_replacement_machine_checkably() -> None:
    """`change` is prose for a reader; `removes`/`adds` are what is enforced."""
    for key, entry in _classes().items():
        assert entry["removes"], key
        assert entry["adds"], key
        assert key in entry["removes"], f"{key} must name the constant it is keyed by"


def test_an_arrival_already_present_elsewhere_is_not_an_arrival() -> None:
    """Why `adds` is containment, not equality.

    The `Set` subset class adds `LE.le`, and two covered declarations already
    said `LE.le` for another reason, so it never shows up as new. Requiring
    equality would report those two as unexplained.
    """
    assert _accounted({"HasSubset.Subset", "Set.instHasSubset"}, {"Set.instLE"})


def test_a_rearrangement_is_not_a_substitution() -> None:
    """Same constants, different shape: a binder kind, an argument order, a universe.

    No entry in the registry can excuse one of these, so `substitution` must
    report nothing on either side rather than something that might match a key.
    """
    gone, came = drift.substitution("(c A []) (c B [])", "(c B []) (c A [])")
    assert not gone and not came


def test_every_recorded_class_names_an_anchor_that_exists() -> None:
    """A class without a checkable anchor is an assertion, not an adjudication.

    Checking only that `adjudicated_in` exists is too weak: every class names
    the same file, so one file existing for any reason would satisfy all of
    them, including a class with no anchor in it. The `-- class:` marker makes
    the claim per-class, and the CI step that elaborates the file makes the
    anchor beside it a kernel obligation rather than a comment.
    """
    registry = drift.json.loads(drift.CLASSES_PATH.read_text(encoding="utf-8"))
    assert registry["classes"], "the registry is what keeps the human cost flat"
    for entry in registry["classes"]:
        assert entry["anchor"].strip()
        witness = ROOT / entry["adjudicated_in"]
        assert witness.is_file(), entry["key"]
        marked = {
            line.removeprefix("-- class:").strip()
            for line in witness.read_text(encoding="utf-8").splitlines()
            if line.startswith("-- class:")
        }
        assert entry["key"] in marked, (
            f"{entry['key']} is recorded as adjudicated in {entry['adjudicated_in']}, "
            "which contains no `-- class:` line naming it"
        )


def test_the_witness_file_has_no_orphan_class_markers() -> None:
    """The other direction: a marker for a class the registry does not record.

    Without this, a class could be dropped from the registry -- retiring the
    machine-checked accounting for it -- while its anchor stayed behind and the
    file still looked complete to a reader.
    """
    registry = drift.json.loads(drift.CLASSES_PATH.read_text(encoding="utf-8"))
    keys = {entry["key"] for entry in registry["classes"]}
    witnesses = {ROOT / entry["adjudicated_in"] for entry in registry["classes"]}
    for witness in witnesses:
        for line in witness.read_text(encoding="utf-8").splitlines():
            if line.startswith("-- class:"):
                marker = line.removeprefix("-- class:").strip()
                assert marker in keys, f"{witness.name} anchors unrecorded class {marker}"


def test_only_the_last_migration_keeps_its_dumps() -> None:
    """Two sides of one migration, not a dump per toolchain we ever pinned.

    A dump is ~360 KB and Foundation moves monthly. Keeping every one of them
    turns a fixed cost into an accruing one, and the older sides answer nothing
    the adjudication record does not already answer.
    """
    dumps = sorted((ROOT / "docs" / "status").glob("elab-baseline-*.json*"))
    assert len(dumps) <= 2, f"prune the superseded dump(s): {[d.name for d in dumps]}"


# --- The exit policy that makes the comparison gateable ---------------------
#
# `--compare` alone fails on any movement, which is the migration question and
# is red on every ordinary branch, so it sat unwired. `--fatal silent` asks the
# question a branch can be held to. These pin both halves: that ordinary work
# stays green, and that the one bucket the flag keeps still turns it red.


def _dump(tmp_path: Path, name: str, decls: dict) -> Path:
    path = tmp_path / name
    drift.write_dump(
        path,
        {
            "toolchain": "leanprover/lean4:v4.33.0",
            "commit": "0" * 40,
            "modules": 1,
            "selector": "module",
            "raw": True,
            "declarations": decls,
        },
    )
    return path


def test_fatal_silent_passes_a_branch_that_only_adds(tmp_path: Path) -> None:
    """Adding statements is what a branch is for; failing here unwires the gate."""
    base = {"T.foo": _decl("aaaa", "P")}
    old = _dump(tmp_path, "old.json", base)
    new = _dump(tmp_path, "new.json", dict(base) | {"T.new": _decl("bbbb", "Q")})
    assert drift.do_compare(old, new, 0, "silent") == 0
    # The default still answers the migration question and sees the addition.
    assert drift.do_compare(old, new, 0, "any") == 1


def test_fatal_silent_fails_a_statement_that_changed_meaning_silently(tmp_path: Path) -> None:
    """The one bucket the flag keeps. If this passes, the gate checks nothing."""
    old = _dump(tmp_path, "old.json", {"T.foo": _decl("aaaa", "P")})
    new = _dump(tmp_path, "new.json", {"T.foo": _decl("zzzz", "P")})
    assert drift.do_compare(old, new, 0, "silent") == 1


def test_fatal_silent_passes_a_visible_edit_and_a_deletion(tmp_path: Path) -> None:
    """Both are legible in the source and are covered by the source-reading gates."""
    old = _dump(
        tmp_path, "old.json", {"T.foo": _decl("aaaa", "P"), "T.gone": _decl("cccc", "R")}
    )
    new = _dump(tmp_path, "new.json", {"T.foo": _decl("bbbb", "P -> P")})
    assert drift.do_compare(old, new, 0, "silent") == 0


def test_fatal_silent_fails_when_the_dumps_share_nothing(tmp_path: Path) -> None:
    """An empty comparison satisfies a silent-only policy exactly as a clean one
    does, so the denominator has to be checked rather than reported."""
    old = _dump(tmp_path, "old.json", {"T.foo": _decl("aaaa", "P")})
    new = _dump(tmp_path, "new.json", {"U.bar": _decl("bbbb", "Q")})
    assert drift.do_compare(old, new, 0, "silent") == 1


def test_fatal_silent_says_how_many_it_compared(tmp_path: Path, capsys) -> None:
    """A pass that does not report its denominator cannot be told from a pass
    over nothing."""
    same = {"T.foo": _decl("aaaa", "P"), "T.bar": _decl("cccc", "Q")}
    old = _dump(tmp_path, "old.json", same)
    new = _dump(tmp_path, "new.json", dict(same))
    assert drift.do_compare(old, new, 0, "silent") == 0
    assert "2 declaration(s) compared" in capsys.readouterr().out


def test_fatal_is_refused_where_it_would_do_nothing() -> None:
    """--fatal on --classify would read as enforcement and enforce nothing."""
    completed = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "check_elaboration_drift.py"),
            "--classify",
            str(ROOT / "docs" / "status" / "elab-baseline-v4310.json"),
            str(ROOT / "docs" / "status" / "elab-baseline-v4330.json"),
            "--fatal",
            "silent",
        ],
        capture_output=True,
        text=True,
    )
    assert completed.returncode != 0
    assert "--fatal only means anything with --compare" in completed.stderr


def test_the_recorded_migration_is_red_under_the_gate_policy() -> None:
    """The committed pair is a real silent set, so it exercises the red path."""
    assert (
        drift.do_compare(
            ROOT / "docs" / "status" / "elab-baseline-v4310.json",
            ROOT / "docs" / "status" / "elab-baseline-v4330.json",
            0,
            "silent",
        )
        == 1
    )


def test_the_live_comparison_is_wired_into_ci() -> None:
    """The gap this closes: the checker existed and CI ran none of it.

    Pinned by text because the failure mode is silent -- the script keeps
    working, the baseline stays committed, and nothing runs it.
    """
    workflow = (ROOT / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")
    assert "--fatal silent" in workflow, "CI does not enforce the silent bucket"
    assert "docs/status/elab-baseline-v4330.json" in workflow, (
        "CI enforces --fatal silent against something other than the committed baseline"
    )
    gate = (ROOT / "scripts" / "agent_gate.sh").read_text(encoding="utf-8")
    assert "--classify" in gate, "the gate does not check the adjudication accounting"


def test_the_fingerprint_is_hashed_outside_lean() -> None:
    """The digest must not depend on which Lean version rendered the expression.

    `String.hash` is an implementation detail of the toolchain being compared. If
    the harness hashed there, a v4.31 digest and a v4.33 digest would disagree on
    every declaration and the report would be unreadable in precisely the case it
    is written for.
    """
    source = drift.harness_source(["AISafetyAtlas"])
    assert ".hash" not in source
    assert "hashlib" in Path(drift.__file__).read_text(encoding="utf-8")


def test_the_normalizer_is_shared_by_the_sweep_and_the_self_test() -> None:
    """A self-test that validated a different encoding would validate nothing."""
    body = "\n".join(drift.NORMALIZER)
    assert body in drift.harness_source(["AISafetyAtlas"])
    assert body in drift.selftest_source()


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
    assert drift.built_modules(tmp_path) == ["AISafetyAtlas", "AISafetyAtlas.Live"]


def test_a_source_outside_every_target_is_still_not_a_module(tmp_path: Path) -> None:
    """The other half, and the reason discovery is artifact-based to begin with:
    a `.lean` that no target builds must not become an import error."""
    _fake_tree(
        tmp_path,
        sources=["AISafetyAtlas", "AISafetyAtlas.Live", "AISafetyAtlas.Unbuilt"],
        oleans=["AISafetyAtlas", "AISafetyAtlas.Live"],
    )
    assert drift.built_modules(tmp_path) == ["AISafetyAtlas", "AISafetyAtlas.Live"]
