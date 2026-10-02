#!/usr/bin/env python3
"""Report shipped theorems that no witness or citation ever reaches.

`report_consumers.py` answers "does anything depend on this?" over the
declarations the registry cites. This answers a different question over a wider
surface: **is this theorem grounded?** A theorem is grounded when it is cited in
`registry.yaml`, or applied somewhere under `AISafetyAtlas/Examples/`, or
applied by a declaration that is itself grounded.

An ungrounded theorem is not wrong and its proof is not suspect. Nothing in the
tree reaches it, so the window it lives in is between building a theorem and
connecting it to anything — `Wireheading.ProgramPrior`'s
`actionValue_eq_programSum` sat there, named in registry *prose* and nowhere
else, invisible to every existing check.

**Two numbers are reported, because "grounded" is weaker than "applied".** A
`registry.yaml` citation grounds a theorem, and a citation is a human saying the
theorem matters — it is not built, so it cannot distinguish a satisfiable
antecedent from an unsatisfiable one. Only an `Examples/` application does that.
So the second line reports the theorems no application reaches, which is the
*silent-vacuity* number and is always the larger of the two. Quote whichever
answers the question being asked, and say which one it is; quoting the first as
though it were the second overstates how much of the library the build exercises.

Grounding is transitive on purpose. Witnessing a leaf grounds everything that
flows into it, so the work is bounded by the leaves rather than by the whole
ungrounded set.

**A witness is not a consumer, and this is not the consumer work queue.**
`report_consumers.py` asks whether anything *depends* on a declaration; zero
there means no demand yet, which for shared infrastructure built ahead of its
consumers is not a defect, and its remedy -- give it a consumer or retire it --
does not apply here. This report asks whether anything *instantiates* the
hypotheses. A law written years before its first consumer can still be applied
once at a toy model, and that is the whole obligation: **the fix is always an
`Examples/` instance, never a manufactured consumer and never a deletion.**
Deleting a zero-consumer lemma to satisfy this report would be the wrong repair
to the wrong problem.

Accuracy. Declaration identity comes from `docs/status/declaration-index.json`,
which the build generates, never from the module path: a declaration's namespace
is not its module, and `AISafetyAtlas.Analysis.Semialgebraic::IsSemialgebraic.basic`
in the public API pin is really `AISafetyAtlas.Analysis.IsSemialgebraic.basic`.
Uses are matched the way `report_consumers.py` matches them — any dotted suffix
of the declaration's own name, in a module that can see the definition site
through the local import graph, with comments and string literals masked — but
attributed to the *enclosing declaration* rather than to the module, because
module granularity cannot carry a chain.

Dot notation is matched, and for this report it has to be.
`(twoDecisionCID.mem_decisions_iff w).mpr` is how the call is written, and no
*prefix* of that run is a suffix of the declaration's name. Matching prefixes
alone — which is all a "does anything use this?" report needs — reports a
theorem as reaching no witness while its witness sits in `Examples/`, so for a
debt report it manufactures the debt rather than conceding it.

**A leaf whose antecedent is provably empty is a third thing, and it is recorded
rather than silently dropped.** `Causal.O24Solution.marginClass_subset` takes an
`O24Solution`, and `Examples.Causal.O24Refutation.isEmpty_o24Solution` proves no
such term exists, so no `Examples/` application can ever be written: the work
this report normally asks for does not exist to be done. Counting it as ordinary
debt says work is owed that is not, and excluding it silently is the exact
failure this report was built against -- an unsatisfiable antecedent must never
be indistinguishable from an unwitnessed one.

So `docs/status/witness-vacuity.json` records each such theorem with the empty
type and the declaration that proves it empty, and the entry is **checked, not
believed**: both names must exist in the declaration index, and the theorem must
still be an unwitnessed leaf. The theorem stays in the ungrounded and unapplied
counts, because nothing in the build does exercise it and that is true; what
changes is that it leaves the **work queue**, with the reason named. Inhabit
`O24Solution` and the emptiness proof goes away with it, and this check fails --
which is what makes the disposition a claim rather than an exemption.

Known limits. Most push the reported debt down; the last pushes it up, and the
distinction matters because it is a claim about which direction the error runs:

* A bare leaf mention is refused when more than one declaration in the tree
  carries that leaf, since it is evidence for all of them and so for none.
  Ambiguity is measured over the atlas index alone, so a leaf shared with a
  Mathlib name is not caught.
* `open` and shadowing are not resolved as the elaborator resolves them.
* A declaration used only inside a `private` proof its span misattributes is
  reported as used.
* Vendored declarations are excluded from the surface, but vendored *files* are
  still read as use sites, so vendored code can ground an atlas theorem.
* **Upward:** a lemma applied only through its `@[simp]` tag is never named, so
  `simp [foo]` grounds `foo` while a bare `simp` does not. Such a lemma reads as
  ungrounded although the build does exercise it.

`--since REF` is the ratchet, and it stores nothing. Everything this report
reads is already tracked — the Lean sources, the generated declaration index,
the public API pin, the registry — so the prior state is *derivable*: materialize
REF with `git archive` and compare. A checked-in baseline would be a second copy
of what git already holds, and one regenerated from the working tree would equal
the working tree and detect nothing.

It compares **identities**, never a count, because a count lets one commit
discharge an obligation and introduce a different one, netting zero and passing.
At `--since HEAD~1` that is the roadmap's P1.2 rule exactly: the witness lands in
the same commit as the hypothesis bundle.

Usage:
    python3 scripts/check_witness_debt.py
    python3 scripts/check_witness_debt.py --leaves          # only the work queue
    python3 scripts/check_witness_debt.py --since HEAD~1    # CI: no new ungrounded
"""

from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))

from validate_current_state import (  # noqa: E402
    dependency_closure,
    lean_code_without_comments_or_strings,
    local_imports,
)

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = "registry.yaml"
DECLARATION_INDEX = "docs/status/declaration-index.json"
PUBLIC_API = "docs/status/public-api.txt"
VACUITY = "docs/status/witness-vacuity.json"
LEAN_DIR = "AISafetyAtlas"
EXAMPLES_PREFIX = "AISafetyAtlas.Examples"

# Third-party code vendored under a pinned revision. The atlas checks its own
# results against it; it is not an atlas result and carries no atlas obligation.
VENDORED_PREFIXES = ("AISafetyAtlas.Upstream.",)

# A use is the (module, declaration) that applies something. An `Examples/`
# use collapses to one sentinel of the same shape: what matters is that a
# witness reached it, not which witness did.
Use = tuple[str, str]
EXAMPLE_USE: Use = ("<example>", "<example>")

DEFINITION = "(?:theorem|lemma|def|abbrev|instance|structure|inductive)"
DECLARATION_START = re.compile(
    rf"(?m)^\s*(?:@\[[^\]]*\]\s*)?"
    rf"(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+)*"
    rf"{DEFINITION}\s+([\w'.]+)"
)
TOKEN = re.compile(r"[\w'.]+")


def lean_sources(root: Path) -> dict[str, tuple[Path, str]]:
    """module -> (path, code with comments and string literals masked).

    The root facade lives beside the directory, not inside it. Omitting it
    severs the import graph: every `Examples/` module reaches the atlas through
    `import AISafetyAtlas`, so without the root nothing is visible from anywhere
    and every declaration looks ungrounded.
    """
    paths = [root / "AISafetyAtlas.lean", *sorted((root / LEAN_DIR).rglob("*.lean"))]
    return {
        ".".join(path.relative_to(root).with_suffix("").parts): (
            path,
            without_hash_commands(
                lean_code_without_comments_or_strings(path.read_text(encoding="utf-8"))
            ),
        )
        for path in paths
    }


HASH_COMMAND = re.compile(r"^[ \t]*#[A-Za-z_]+.*$", re.MULTILINE)


def without_hash_commands(code: str) -> str:
    """Blank `#check`/`#print`/`#eval` lines, keeping offsets intact.

    A `#check` elaborates a type and instantiates nothing, so it is not evidence
    that a hypothesis can be satisfied. This matters more than it sounds:
    `AISafetyAtlas/Examples/Registry.lean` is *generated* from `registry.yaml`
    and is 339 `#check` lines, so without this every registry name would read as
    an `Examples/` witness by way of a file no human wrote.

    Only a `#` that opens a line is a command. `#[1, 2, 3]` is array notation and
    is left alone. A command whose arguments wrap onto a second line still leaks
    that line; no such command exists in the tree today.
    """
    return HASH_COMMAND.sub(lambda m: " " * len(m.group(0)), code)


def visibility(sources: dict[str, tuple[Path, str]]) -> dict[str, set[str]]:
    """module -> every local module it can see through the import graph."""
    modules = set(sources)
    graph = {module: local_imports(code, modules) for module, (_, code) in sources.items()}
    return {module: dependency_closure(module, graph) for module in modules}


def load_index(root: Path) -> tuple[dict[str, str], dict[str, str]]:
    """Declaration name -> kind, and declaration name -> defining module.

    The index is generated from the built environment, so it is the only place
    a declaration's real name and its real home are both recorded.
    """
    payload = json.loads((root / DECLARATION_INDEX).read_text(encoding="utf-8"))
    kinds: dict[str, str] = {}
    homes: dict[str, str] = {}
    for entry in payload["declarations"]:
        if entry["kind"] == "module":
            continue
        kinds[entry["name"]] = entry["kind"]
        homes[entry["name"]] = entry["module"]
    return kinds, homes


def load_pinned(root: Path, homes: dict[str, str]) -> set[str]:
    """The public API pin, resolved to real declaration names.

    A pin line is `module::suffix`, and the suffix is what remains after the
    namespace the module contributes — not a path component, so the full name
    is never the concatenation. Resolve inside the module, where the suffix is
    unique.
    """
    by_module: dict[str, list[str]] = collections.defaultdict(list)
    for name, module in homes.items():
        by_module[module].append(name)

    pinned: set[str] = set()
    unresolved: list[str] = []
    for line in (root / PUBLIC_API).read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if "::" not in line:
            continue
        module, suffix = line.split("::", 1)
        if module.startswith(EXAMPLES_PREFIX):
            continue
        matches = [
            name
            for name in by_module.get(module, ())
            if name == suffix or name.endswith("." + suffix)
        ]
        if len(matches) == 1:
            pinned.add(matches[0])
        elif not module.startswith(VENDORED_PREFIXES):
            # Vendored modules are not on the atlas root import, so the
            # generated index never sees them. That is expected, not a defect.
            unresolved.append(f"{module}::{suffix}")
    if unresolved:
        print(
            f"check_witness_debt: {len(unresolved)} pin lines did not resolve to a "
            f"declaration; first few: {unresolved[:5]}",
            file=sys.stderr,
        )
    return pinned


def qualified_forms(declaration: str) -> list[str]:
    """Every dotted suffix of `declaration`, longest first.

    Lean lets a consumer name a declaration fully, relative to an enclosing
    namespace, or bare, and all three are uses. `Other.foo` is a different
    `foo` and must not count, which is why these are suffixes and not
    substrings.
    """
    parts = declaration.split(".")
    return [".".join(parts[index:]) for index in range(len(parts))]


# Text before the first declaration belongs to no declaration, but it is not
# empty: `example : … := foo` carries no name, and a file that opens with a run
# of examples puts real uses there. Attributing them to this sentinel keeps them
# counted. Dropping the region instead under-credits uses, which for a debt
# report invents debt -- `Examples/Wireheading/RewardGrid.lean` applies
# `gridVal_zero` and `gridVal_last` in exactly that position.
PREAMBLE_OWNER = "<preamble>"


def declaration_spans(code: str) -> list[tuple[str, int, int]]:
    """(name as written, start, stop) for each declaration in one module."""
    starts = [(match.group(1), match.start()) for match in DECLARATION_START.finditer(code)]
    spans: list[tuple[str, int, int]] = []
    if not starts:
        return [(PREAMBLE_OWNER, 0, len(code))]
    if starts[0][1] > 0:
        spans.append((PREAMBLE_OWNER, 0, starts[0][1]))
    for position, (name, start) in enumerate(starts):
        stop = starts[position + 1][1] if position + 1 < len(starts) else len(code)
        spans.append((name, start, stop))
    return spans


def names_in(text: str) -> set[str]:
    """Every name a use inside `text` could be naming.

    Prefixes at dot boundaries carry the written forms: `A`, `A.B`, `A.B.c` for
    `A.B.c.d`. Suffixes carry **dot notation**, and for this report they are not
    optional. `(twoDecisionCID.mem_decisions_iff w).mpr` is how Lean is actually
    written, and no prefix of that run is a suffix of
    `AISafetyAtlas.Causal.CID.mem_decisions_iff`. Collecting prefixes alone
    reports a theorem as reaching no witness while its witness sits in
    `Examples/`, which for a debt report manufactures the debt instead of
    conceding it.

    The over-acceptance this admits is the bare leaf — `cw.sameObservation` is
    evidence for every `sameObservation` in the tree. `build_uses` refuses the
    bare leaf wherever more than one declaration carries it.
    """
    found: set[str] = set()
    for run in TOKEN.findall(text):
        parts = [part for part in run.split(".") if part]
        for stop in range(1, len(parts) + 1):
            found.add(".".join(parts[:stop]))
            found.add(".".join(parts[len(parts) - stop:]))
    return found


def build_uses(
    sources: dict[str, tuple[Path, str]],
    visible: dict[str, set[str]],
    homes: dict[str, str],
    tracked: set[str],
) -> dict[str, set[Use]]:
    """declaration -> the declarations that apply it, with `Examples/` collapsed."""
    ambiguous_leaves = collections.Counter(name.split(".")[-1] for name in homes)
    forms: dict[str, list[str]] = {}
    for declaration in tracked:
        candidates = qualified_forms(declaration)
        if ambiguous_leaves[declaration.split(".")[-1]] > 1:
            candidates = candidates[:-1]
        forms[declaration] = candidates

    by_form: dict[str, set[str]] = collections.defaultdict(set)
    for declaration, candidates in forms.items():
        for form in candidates:
            by_form[form].add(declaration)

    uses: dict[str, set[Use]] = collections.defaultdict(set)
    for module, (path, code) in sources.items():
        in_examples = module.startswith(EXAMPLES_PREFIX)
        reachable = visible.get(module, set())
        for owner, start, stop in declaration_spans(code):
            span_names = names_in(code[start:stop])
            for form in span_names & by_form.keys():
                for declaration in by_form[form]:
                    if homes.get(declaration) not in reachable:
                        continue
                    if not in_examples and owner in qualified_forms(declaration):
                        continue  # the definition site is not a use
                    uses[declaration].add(EXAMPLE_USE if in_examples else (module, owner))
    return uses


def cited_declarations(root: Path) -> set[str]:
    """Every declaration the registry names, through **both** of its channels.

    `lean_artifact.declarations` is a list of objects keyed by
    `atlas_declaration`; `formalizations[].declarations` is a list of plain
    strings. `report_consumers.py` reads only the first, which is why its
    surface is 321 declarations rather than the whole ledger. A grounding
    report that read only the first would call a fully cited theorem
    ungrounded — `Causal.CID.decisions_disjoint_utilities` is cited in the
    second and in no other place.
    """
    registry = json.loads((root / REGISTRY).read_text(encoding="utf-8"))
    cited: set[str] = set()
    for result in registry["results"]:
        artifact = result.get("lean_artifact")
        if artifact is not None:
            for declaration in artifact["declarations"]:
                cited.add(declaration["atlas_declaration"])
        for formalization in result.get("formalizations") or ():
            for declaration in formalization.get("declarations") or ():
                cited.add(
                    declaration
                    if isinstance(declaration, str)
                    else declaration["atlas_declaration"]
                )
    return cited


def grounded_set(
    tracked: set[str],
    uses: dict[str, set[Use]],
    covered: set[str],
    owner_of: dict[Use, str],
) -> set[str]:
    """Declarations a witness or a citation reaches, directly or through a chain."""
    memo: dict[str, bool] = {}

    def reaches(declaration: str, stack: frozenset[str]) -> bool:
        if declaration in memo:
            return memo[declaration]
        if declaration in covered:
            memo[declaration] = True
            return True
        if declaration in stack:
            return False  # a cycle grounds nothing on its own
        result = False
        for user in uses.get(declaration, ()):
            if user == EXAMPLE_USE:
                result = True
                break
            consumer = owner_of.get(user)
            if consumer is None:
                continue
            if reaches(consumer, stack | {declaration}):
                result = True
                break
        memo[declaration] = result
        return result

    sys.setrecursionlimit(10000)
    return {name for name in tracked if reaches(name, frozenset())}


def examples_file_for(module: str) -> Path | None:
    """The `Examples/` file that would hold a witness for `module`, if one exists.

    `Examples/` does not mirror the library tree exactly. Most files sit at the
    mirrored path, but a nested library module is often flattened -- the witness
    for `AISafetyAtlas.Inference.Stochastic.Sharpness` lives in
    `Examples/Inference/Sharpness.lean`, and for `…Stochastic.Approximation` in
    `Examples/Inference/StochasticApproximation.lean`. Guessing only the mirror
    reported six modules as having no example file when all six had one, which
    turns a queue entry from "write a witness" into "write a file" and is the
    more expensive of the two by a wide margin.
    """
    parts = module.split(".")[1:]
    if not parts:
        return None
    candidates = [
        Path(LEAN_DIR, "Examples", *parts).with_suffix(".lean"),
        Path(LEAN_DIR, "Examples", parts[0], "".join(parts[1:])).with_suffix(".lean"),
        Path(LEAN_DIR, "Examples", *parts[:-1], parts[-1]).with_suffix(".lean"),
        Path(LEAN_DIR, "Examples", parts[0], parts[-1]).with_suffix(".lean"),
    ]
    for candidate in candidates:
        if (ROOT / candidate).exists():
            return candidate
    return None


def analyse(root: Path) -> tuple[list[str], list[str], int, list[str], list[str]]:
    """(ungrounded, leaves, pinned theorem count, unapplied, unapplied leaves).

    The last two answer the vacuity question on its own: which theorems no
    `Examples/` application reaches, whether or not a human has cited them. That
    set is always at least the first, because a citation grounds and does not
    apply.

    **Both metrics get a leaf list, and until 2026-09-21 only one did.** The
    unapplied set was reduced to its length here and thrown away, so the number
    this repository quotes for silent vacuity -- the larger, and the one that
    distinguishes a satisfiable antecedent from an unsatisfiable one -- had no
    work queue, while the weaker number had one. Leaves are what bound the work
    in both cases, since grounding is transitive: 299 unapplied theorems sat on
    185 leaves when this was first computed, so two thirds of that set grounds
    for free once the heads are witnessed.
    """
    kinds, homes = load_index(root)
    pinned = load_pinned(root, homes)
    sources = lean_sources(root)
    visible = visibility(sources)

    tracked = {name for name in pinned if not name.startswith(VENDORED_PREFIXES)}
    uses = build_uses(sources, visible, homes, set(homes))

    owner_of: dict[Use, str] = {}
    for name, module in homes.items():
        for form in qualified_forms(name):
            owner_of[(module, form)] = name

    applied = {name for name in homes if EXAMPLE_USE in uses.get(name, ())}
    covered = cited_declarations(root) | applied
    grounded = grounded_set(set(homes), uses, covered, owner_of)

    theorems = {name for name in tracked if kinds.get(name) == "theorem"}
    ungrounded = sorted(theorems - grounded)

    # The same fixpoint with citation removed. A `registry.yaml` line records
    # that a human connected the theorem to a result; it does not instantiate a
    # hypothesis, so it cannot distinguish a satisfiable antecedent from an
    # unsatisfiable one. Both numbers are reported because they answer different
    # questions and only one of them is the vacuity question.
    unapplied_any = theorems - grounded_set(set(homes), uses, applied, owner_of)
    unapplied = sorted(unapplied_any)

    def heads(names: list[str], within: set[str]) -> list[str]:
        """The names in `names` that no other member of `within` flows into.

        `EXAMPLE_USE` is skipped because a use from `Examples/` is what grounds a
        theorem rather than what makes it depend on another ungrounded one.
        """
        return sorted(
            name
            for name in names
            if not {
                owner_of.get(user)
                for user in uses.get(name, ())
                if user != EXAMPLE_USE
            }
            & within
        )

    leaves = heads(ungrounded, set(ungrounded))
    unapplied_leaves = heads(unapplied, unapplied_any)
    return ungrounded, leaves, len(theorems), unapplied, unapplied_leaves


def load_vacuity(root: Path) -> dict[str, dict[str, str]]:
    """Leaves whose antecedent is provably uninhabited, each with its proof."""
    path = root / VACUITY
    if not path.exists():
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    return dict(payload.get("declarations", {}))


def check_vacuity(
    entries: dict[str, dict[str, str]], leaves: list[str], known: set[str]
) -> list[str]:
    """Every recorded disposition still names real declarations and a real leaf.

    Three ways an entry can go bad, and each is a failure rather than a warning.
    The theorem can stop existing. It can stop being an unwitnessed leaf --
    someone found a way to apply it after all, so the disposition is now a
    licence to ignore a theorem the build does reach. Or the emptiness proof can
    stop existing, which is what happens the day somebody inhabits the type, and
    is precisely when a reader must be told that the leaf is ordinary debt again.
    """
    problems: list[str] = []
    leaf_set = set(leaves)
    for name, record in sorted(entries.items()):
        if name not in known:
            problems.append(f"{name} carries a vacuity entry but is not a declaration here")
            continue
        if name not in leaf_set:
            problems.append(
                f"{name} carries a vacuity entry but is no longer an unwitnessed leaf"
            )
        empty_type = str(record.get("empty_type", "")).strip()
        proof = str(record.get("emptiness_proof", "")).strip()
        if not empty_type or not proof:
            problems.append(
                f"{name} must name both an empty_type and the emptiness_proof for it"
            )
            continue
        for named in (empty_type, proof):
            if named not in known:
                problems.append(
                    f"{name} names {named}, which is not a declaration in this tree"
                )
    return problems


def analyse_at(ref: str) -> list[str]:
    """The ungrounded set as of a git ref, materialized into a temporary tree.

    Everything this report reads is tracked -- the Lean sources, the generated
    declaration index, the public API pin and the registry -- so the prior state
    is *derivable* and does not have to be stored. A checked-in baseline would
    be a second copy of something git already holds, and a baseline regenerated
    from the working tree would equal the working tree and detect nothing.
    """
    with tempfile.TemporaryDirectory(prefix="atlas-witness-") as directory:
        archive = subprocess.run(
            ["git", "archive", ref], cwd=ROOT, stdout=subprocess.PIPE, check=True
        )
        subprocess.run(
            ["tar", "-x", "-C", directory], input=archive.stdout, check=True
        )
        return analyse(Path(directory))[0]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--leaves", action="store_true", help="print only the work queue")
    parser.add_argument(
        "--module",
        default="",
        help="with --leaves, restrict the queue to one module prefix, "
        "as AISafetyAtlas.Sovereignty.",
    )
    parser.add_argument("--json", type=Path, help="write the full report to this path")
    parser.add_argument(
        "--since",
        metavar="REF",
        help=(
            "fail when a theorem is ungrounded here that was not ungrounded at "
            "REF (for example HEAD~1, or the merge base with main)"
        ),
    )
    parser.add_argument(
        "--max-ungrounded",
        type=int,
        metavar="N",
        help="fail when more than N theorems are ungrounded (the ceiling ratchet)",
    )
    parser.add_argument(
        "--max-unapplied",
        type=int,
        metavar="N",
        help="fail when more than N theorems reach no Examples/ application",
    )
    arguments = parser.parse_args()

    ungrounded, leaves, theorem_count, unapplied, unapplied_leaves = analyse(ROOT)

    vacuity = load_vacuity(ROOT)
    vacuity_problems = check_vacuity(vacuity, leaves, set(load_index(ROOT)[0]))
    # A leaf with a recorded, checked emptiness proof is not work anybody can do.
    # It stays in the counts above -- nothing exercises it, which is true -- and
    # leaves the queue with its reason attached.
    unwitnessable = [name for name in leaves if name in vacuity]
    workable = [name for name in leaves if name not in vacuity]

    print(
        f"check_witness_debt: {theorem_count} pinned theorems, "
        f"{len(ungrounded)} ungrounded, {len(leaves)} of those are leaves"
    )
    if unwitnessable:
        print(
            f"  {len(unwitnessable)} leaf/leaves cannot be witnessed at all: the "
            f"antecedent is provably uninhabited, with the proof named in "
            f"{VACUITY}. They are counted above and are not work:"
        )
        for name in unwitnessable:
            record = vacuity[name]
            print(f"    {name}")
            print(f"        {record['empty_type']} is empty by {record['emptiness_proof']}")
    unapplied_workable = [name for name in unapplied_leaves if name not in vacuity]
    print(
        f"  {len(unapplied)} reach no Examples/ application at all, on "
        f"{len(unapplied_leaves)} leaves "
        f"(the {len(ungrounded)} above also counts a registry citation as grounding, "
        f"and a citation instantiates nothing)"
    )
    if unapplied_workable:
        by_cluster = collections.Counter(
            name.split(".")[1] for name in unapplied_workable
        )
        print(
            "  silent-vacuity leaves by cluster: "
            + ", ".join(f"{c} {n}" for c, n in by_cluster.most_common())
        )
        print(
            "  That second queue is the one to work: grounding is transitive, so "
            "witnessing a head grounds everything flowing into it, and a witness "
            "that only moves the counter is worth nothing -- inhabit the "
            "hypotheses at values where the conclusion says something, or prove "
            f"the antecedent empty and record it in {VACUITY}."
        )
    if ungrounded:
        by_cluster = collections.Counter(name.split(".")[1] for name in workable)
        print("  leaves by cluster: " + ", ".join(
            f"{cluster} {count}" for cluster, count in by_cluster.most_common()
        ))
        print(
            "  A leaf is the head of an ungrounded chain: nothing grounded "
            "reaches it, and no ungrounded theorem depends on it either, so it "
            "is where the work starts. Apply it once in Examples/ -- a consumer "
            "is not what is missing. A leaf reached by no application at all is "
            "also unfalsifiable by the build: an unsatisfiable antecedent would "
            "look exactly the same."
        )
    leaf_set = set(leaves)
    if not arguments.leaves:
        for name in ungrounded:
            print(f"    {'leaf ' if name in leaf_set else '     '}{name}")
    else:
        # The queue, grouped by the module that owns each head, because the unit
        # of work is one `Examples/` file and not one theorem: a module's heads
        # share a carrier, so they are witnessed together or not at all.
        homes = load_index(ROOT)[1]
        queue = [
            name
            for name in unapplied_workable
            if not arguments.module or homes.get(name, "").startswith(arguments.module)
        ]
        by_module: dict[str, list[str]] = collections.defaultdict(list)
        for name in queue:
            by_module[homes.get(name, "?")].append(name)
        for module, names in sorted(
            by_module.items(), key=lambda kv: (-len(kv[1]), kv[0])
        ):
            mirror = examples_file_for(module)
            where = "witness goes in" if mirror is not None else "no file yet, try"
            shown = mirror if mirror is not None else Path(
                LEAN_DIR, "Examples", *module.split(".")[1:]
            ).with_suffix(".lean")
            print(f"  {len(names):3d}  {module}  ({where} {shown})")
            for name in names:
                print(f"         {name}")
        if workable:
            print("  also ungrounded and unapplied, with no citation either:")
            for name in workable:
                print(f"         {name}")

    if vacuity_problems:
        for problem in vacuity_problems:
            print(f"check_witness_debt: {problem}", file=sys.stderr)
        print(
            f"check_witness_debt: a vacuity disposition is a claim about the tree, "
            f"not an exemption from it. Fix {VACUITY}, or witness the theorem.",
            file=sys.stderr,
        )
        return 1

    if arguments.json:
        arguments.json.write_text(
            json.dumps(
                {
                    "generated_by": "scripts/check_witness_debt.py --json",
                    "counts": {
                        "pinned_theorems": theorem_count,
                        "ungrounded": len(ungrounded),
                        "leaves": len(leaves),
                        "unwitnessable_leaves": len(unwitnessable),
                        "unapplied": len(unapplied),
                        "unapplied_leaves": len(unapplied_leaves),
                    },
                    "ungrounded": ungrounded,
                    "leaves": leaves,
                    "unwitnessable": unwitnessable,
                    "unapplied": unapplied,
                    "unapplied_leaves": unapplied_leaves,
                    "unapplied_work_queue": unapplied_workable,
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )

    # Ceilings. `--since` is the better ratchet because it compares identities,
    # but it needs a ref and a second tree; these are what the cheap gate can
    # afford on every run, and they are what stops a slow drift back.
    over = []
    if arguments.max_ungrounded is not None and len(ungrounded) > arguments.max_ungrounded:
        over.append(f"{len(ungrounded)} ungrounded exceeds the pinned {arguments.max_ungrounded}")
    if arguments.max_unapplied is not None and len(unapplied) > arguments.max_unapplied:
        over.append(
            f"{len(unapplied)} unapplied exceeds the pinned {arguments.max_unapplied}"
        )
    if over:
        for line in over:
            print(f"check_witness_debt: {line}", file=sys.stderr)
        print(
            "check_witness_debt: witness the new leaves, or lower the pin "
            "deliberately in scripts/agent_gate.sh and say why",
            file=sys.stderr,
        )
        return 1

    if arguments.since:
        before = set(analyse_at(arguments.since))
        # Identities, not a count. A count lets one commit discharge an
        # obligation and introduce a different one, netting zero and passing,
        # which is the trade this report exists to make visible.
        added = sorted(set(ungrounded) - before)
        if added:
            print(
                f"check_witness_debt: {len(added)} theorem(s) became ungrounded "
                f"since {arguments.since}. Apply each in Examples/ at a concrete "
                f"instance, in the commit that introduces it:",
                file=sys.stderr,
            )
            for name in added:
                print(f"    {name}", file=sys.stderr)
            return 1
        settled = len(before) - len(set(ungrounded) & before)
        print(
            f"check_witness_debt: nothing new is ungrounded since "
            f"{arguments.since}; {settled} of its entries are now grounded"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
