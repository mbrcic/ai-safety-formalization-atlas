#!/usr/bin/env python3
"""Test the one step of `atlas-check` that no theorem covers: reading the file.

`AISafetyAtlas.Knowledge.Check` proves that the runner's *normalization* is
harmless — `knowable_congr_observation` and `knowable_congr_property` say that
relabelling values leaves knowability alone, provided the partition survives.
What those theorems cannot see is the step before: turning JSON into a model. A
reader that drops a row, pads a short array, or merges two labels produces a
different model, and every downstream theorem then answers correctly about the
wrong question. `docs/guide/atlas-check.md` named that gap; this closes it by
test, since it is not the kind of claim a proof can carry.

Two batteries, and they pull in opposite directions.

**Refusal.** For every shipped fixture, mutations that make the file mean
something other than what it says must be refused rather than decided: arrays of
the wrong length, ragged rows, non-numeric or negative entries, missing fields,
an unknown schema or kind, a declared count that disagrees with the data, and an
index pointing outside the principals it names. The standard is the one the
guide states — refuse rather than pad.

**Invariance.** The mirror image. Renaming values must *not* change the verdict,
because every predicate here depends on the partition the names induce and on
nothing else. This battery drives the proved invariance through the real binary
rather than trusting that the runner honours it.

The failure it guards against is a reader that merges two labels — capping them,
say, instead of renumbering them. Merged outcomes make a column less separating,
so a real `NO OVERSEER CAN FORCE THE OUTCOME` decays into `THE COUNTING BOUND
DOES NOT APPLY`: the runner contradicting the theorem it prints. That direction
buries a finding rather than inventing one, which is the better way to be wrong
and still a wrong answer.

To confirm this battery is not vacuous, break the relabelling in `runVariety` —
cap the outcome index instead of renumbering it — rebuild `atlas-check`, and run
this script. It exits 1 and names both variety invariance cases.


Exits non-zero on any disagreement. Run from `check_atlas_check.sh`, which owns
the binary.
"""

from __future__ import annotations

import copy
import json
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
BINARY = ROOT / ".lake" / "build" / "bin" / "atlas-check"
MODELS = ROOT / "docs" / "examples" / "atlas-check"

# Lines that carry a verdict rather than commentary. Compared across a
# presentation change; the rest of the output may legitimately echo the input.
VERDICT_RE = re.compile(r"verdict:|HOLDS|FAILS|ABSENT|PRESENT")

# The only place a verdict line quotes a value back from the input.
ECHOED_VALUE_RE = re.compile(r"at value \d+")

# Fields whose length is part of the model rather than free: shortening them is
# a different model and must be refused. `coalition` and `emitted` are excluded
# on purpose — a coalition is a subset and the principal count is the row count,
# so both are legitimately variable and are covered by the index-range case.
FIXED_LENGTH = {"observation", "property", "setup", "conclusion", "target", "hazard"}


def run(model: dict) -> tuple[int, str]:
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as handle:
        json.dump(model, handle)
        path = handle.name
    try:
        done = subprocess.run([str(BINARY), path], capture_output=True, text=True)
    finally:
        pathlib.Path(path).unlink(missing_ok=True)
    return done.returncode, done.stdout + done.stderr


def verdicts(output: str) -> list[str]:
    """The decision lines only, with echoed input values — and nothing else — masked.

    Exactly one verdict line quotes a value back from the input: the device
    check names the target value it probed, so relabelling the target
    legitimately changes `at value 1` to `at value 14`. That one number is
    masked and no other.

    Masking digits generally would be wrong. Witness lines like
    `states 1 and 3 share an observation`
    carry *state indices*, which a relabelling of values must not disturb —
    renaming what a state emits cannot change which pair of states collides. A
    blanket mask made those lines compare equal whatever they said, which is the
    reader-agrees-with-itself failure this whole script exists to catch. They are
    compared exactly.
    """
    lines = [ln.strip() for ln in output.splitlines() if VERDICT_RE.search(ln)]
    return [ECHOED_VALUE_RE.sub("at value #", ln) for ln in lines]


def refusals(model: dict):
    """Mutations a correct reader must refuse."""
    for key, value in model.items():
        if not isinstance(value, list) or key.startswith("_"):
            continue
        nested = bool(value) and isinstance(value[0], list)
        if key in FIXED_LENGTH:
            short = copy.deepcopy(model)
            short[key] = value[:-1]
            yield f"{key}: one entry short", short
            long = copy.deepcopy(model)
            long[key] = value + [value[-1]]
            yield f"{key}: one entry too many", long
        if nested:
            ragged = copy.deepcopy(model)
            ragged[key][0] = ragged[key][0][:-1]
            yield f"{key}: a ragged row", ragged
            wide = copy.deepcopy(model)
            wide[key][0] = wide[key][0] + [0]
            yield f"{key}: an over-long row", wide
        else:
            text = copy.deepcopy(model)
            text[key] = ["x"] + value[1:]
            yield f"{key}: a non-numeric entry", text
            negative = copy.deepcopy(model)
            negative[key] = [-1] + value[1:]
            yield f"{key}: a negative entry", negative

    for key in model:
        if key.startswith("_"):
            continue
        yield f"missing '{key}'", {k: v for k, v in model.items() if k != key}

    bad_schema = copy.deepcopy(model)
    bad_schema["schema"] = "atlas-check/99"
    yield "an unknown schema", bad_schema

    bad_kind = copy.deepcopy(model)
    bad_kind["kind"] = "nonsense"
    yield "an unknown kind", bad_kind

    for key in ("states", "situations", "interventions"):
        if key in model:
            inflated = copy.deepcopy(model)
            inflated[key] = model[key] + 1
            yield f"'{key}' disagreeing with the data", inflated
            zero = copy.deepcopy(model)
            zero[key] = 0
            yield f"'{key}' zero", zero

    if model.get("kind") == "coalition":
        out_of_range = copy.deepcopy(model)
        out_of_range["coalition"] = [len(model["emitted"])]
        yield "a coalition member that is not a principal", out_of_range
        negative = copy.deepcopy(model)
        negative["coalition"] = [-1]
        yield "a negative coalition member", negative
        dropped = copy.deepcopy(model)
        dropped["emitted"] = dropped["emitted"][:-1]
        if max(model["coalition"]) >= len(dropped["emitted"]):
            yield "a dropped principal the coalition still names", dropped


def relabel(values: list[int]) -> list[int]:
    """An injective renaming: distinct in, distinct out, and far from zero."""
    return [v * 3 + 11 for v in values]


def invariances(model: dict):
    """Presentation changes that must leave the verdict alone."""
    kind = model.get("kind")
    if kind == "knowability":
        for key in ("observation", "property"):
            relabelled = copy.deepcopy(model)
            relabelled[key] = relabel(model[key])
            yield f"'{key}' relabelled", relabelled
    elif kind == "device":
        setup = copy.deepcopy(model)
        setup["setup"] = relabel(model["setup"])
        yield "'setup' relabelled", setup
        target = copy.deepcopy(model)
        target["target"] = relabel(model["target"])
        target["value"] = relabel([model["value"]])[0]
        yield "'target' and 'value' relabelled together", target
    elif kind == "coalition":
        emitted = copy.deepcopy(model)
        emitted["emitted"] = [relabel(row) for row in model["emitted"]]
        yield "every principal's evidence relabelled", emitted
    elif kind == "variety":
        effect = copy.deepcopy(model)
        effect["effect"] = [relabel(row) for row in model["effect"]]
        yield "the table's outcomes relabelled", effect
        sparse = copy.deepcopy(model)
        seen = sorted({v for row in model["effect"] for v in row})
        wide = {v: (i + 1) * 997 for i, v in enumerate(seen)}
        sparse["effect"] = [[wide[v] for v in row] for row in model["effect"]]
        yield "the table's outcomes spread far apart", sparse

    reordered = {k: model[k] for k in reversed(list(model))}
    yield "the keys in reverse order", reordered


def main() -> int:
    if not BINARY.is_file():
        print(f"check_atlas_check_parse: {BINARY} is not built", file=sys.stderr)
        return 1

    fixtures = sorted(MODELS.glob("*.json"))
    if not fixtures:
        print("check_atlas_check_parse: no fixtures found", file=sys.stderr)
        return 1

    checks = 0
    failures = 0
    for path in fixtures:
        model = json.loads(path.read_text())
        code, output = run(model)
        if code != 0:
            print(f"FAIL {path.name}: the shipped fixture is refused", file=sys.stderr)
            print(output, file=sys.stderr)
            failures += 1
            continue
        baseline = verdicts(output)

        for label, mutated in refusals(model):
            mutant_code, mutant_output = run(mutated)
            if mutant_code == 0:
                print(
                    f"FAIL {path.name}: accepted {label} instead of refusing it",
                    file=sys.stderr,
                )
                print(mutant_output, file=sys.stderr)
                failures += 1
            else:
                checks += 1

        for label, mutated in invariances(model):
            mutant_code, mutant_output = run(mutated)
            if mutant_code != 0:
                print(
                    f"FAIL {path.name}: refused {label}, which is a presentation "
                    "change and not a different model",
                    file=sys.stderr,
                )
                print(mutant_output, file=sys.stderr)
                failures += 1
            elif verdicts(mutant_output) != baseline:
                print(
                    f"FAIL {path.name}: {label} changed the verdict",
                    file=sys.stderr,
                )
                print(f"  was: {baseline}", file=sys.stderr)
                print(f"  now: {verdicts(mutant_output)}", file=sys.stderr)
                failures += 1
            else:
                checks += 1

    if failures:
        print(
            f"check_atlas_check_parse: the reader disagrees with its own model in "
            f"{failures} place(s)",
            file=sys.stderr,
        )
        return 1

    print(
        f"atlas-check parse ok: {checks} checks over {len(fixtures)} fixtures — "
        "malformations refused, presentation changes ignored"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
