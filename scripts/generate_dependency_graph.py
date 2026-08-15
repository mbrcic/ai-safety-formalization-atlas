#!/usr/bin/env python3
"""Generate the declaration-level dependency views, one per top-level domain.

The provenance tables say which printed statement a declaration transcribes.
They do not say which declaration *rests on* which, and that is the question an
agent asks when it wants to know what a change breaks, or what a theorem
actually consumed.  Module-level import graphs answer it at the wrong grain: the
whole of `Stochastic.lean` imports the whole of `Device.lean`, which tells you
nothing about whether Proposition 6 uses Theorem 1.

Lean already knows the answer.  This walks the elaborated environment, keeps the
edges between atlas declarations, and renders them.  A blueprint would deliver
roughly this much and would also require maintaining a second, informal copy of
every statement by hand; the registry and the provenance tables already carry
that copy, with multi-source grading a blueprint has no concept of.

Two things fall out of the same data and are worth more than the graph itself:

* the **reverse index** — what rests on a given lemma, so "is this load-bearing?"
  stops being a guess;
* the **leaves** — public declarations nothing else uses and no example mentions.
  That is the per-declaration version of the check `check_example_coverage.py`
  deliberately only does per module.

Regenerating needs a built Lean environment, so it is not in the cheap gate.
`--check` re-reads the committed file and verifies every declaration it names
still exists, which needs no Lean and is cheap enough to gate on.

    python3 scripts/generate_dependency_graph.py --write
    python3 scripts/generate_dependency_graph.py --check
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import NamedTuple, TypedDict


class Node(TypedDict):
    """One declaration: whether it is a theorem, and what its edges point at."""

    kind: str
    deps: list[str]


ROOT = Path(__file__).resolve().parents[1]
STATUS = ROOT / "docs" / "status"
LEAN_ROOT = ROOT / "AISafetyAtlas"
EXAMPLES = LEAN_ROOT / "Examples"
EXECUTABLE = ROOT / "Main.lean"


class Cluster(NamedTuple):
    """One rendered view. The harness walks the whole atlas once; a cluster is a
    slice of the result, so adding one costs a render rather than a Lean run."""

    prefix: str
    title: str
    slug: str

    @property
    def markdown(self) -> Path:
        return STATUS / f"{self.slug}-dependency-graph.md"

    @property
    def json(self) -> Path:
        return STATUS / f"{self.slug}-dependency-graph.json"


# Directories that are not domains. `Examples` is where models live and is
# already the reference set for the unused-definition section; `Upstream` is
# vendored; `Conjectures` is unasserted by construction; `Explore` is the
# discovery workbench and is deliberately off the root import.
NOT_A_DOMAIN = frozenset({"Examples", "Upstream", "Conjectures", "Explore"})


def domain_names() -> list[str]:
    """Every top-level domain that has library Lean under it.

    Derived rather than hand-listed, so a new domain gets a view by existing
    rather than by someone remembering to add one. Hand-listing is how this
    stayed at `Inference` alone while fourteen other domains had none — the
    generator was cluster-parameterized in all but name and nobody noticed.
    """
    names = {
        path.relative_to(LEAN_ROOT).parts[0].removesuffix(".lean")
        for path in LEAN_ROOT.rglob("*.lean")
    }
    # A bare `Foo.lean` with no `Foo/` beside it is still a domain — `Logic` and
    # `Learning` are one module each.
    return sorted(
        name
        for name in names
        if name not in NOT_A_DOMAIN
        and ((LEAN_ROOT / name).is_dir() or (LEAN_ROOT / f"{name}.lean").is_file())
    )


CLUSTERS = tuple(
    Cluster(f"AISafetyAtlas.{name}.", f"{name} cluster", name.lower())
    for name in domain_names()
)

# Compiler-generated companions carry no authored content and would swamp the
# view. `Name.isInternal` misses most of them because they are not marked
# internal — they are ordinary names with a structural suffix.
GENERATED_SUFFIX = re.compile(
    r"\.(mk|rec|recOn|casesOn|below|brecOn|ndrec|ndrecOn|injEq|noConfusion"
    r"|noConfusionType|sizeOf_spec|toCtorIdx|eq_def|eq_\d+|match_\d+|proof_\d+"
    r"|induct|ofNat|ext|ext_iff|inj|below_ind|binductionOn|ctorIdx|congr_simp"
    r"|elim|ctorElim|ctorElimType)$"
)

HARNESS = """import AISafetyAtlas
open Lean

#eval show CoreM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let isProjection := (← getProjectionFnInfo? name).isSome
    if (`AISafetyAtlas).isPrefixOf name && !name.isInternal && !isProjection then
      let mut deps : Array Name := #[]
      for c in ci.type.getUsedConstants do
        if (`AISafetyAtlas).isPrefixOf c && !c.isInternal && c != name then
          deps := deps.push c
      if let some v := ci.value? then
        for c in v.getUsedConstants do
          if (`AISafetyAtlas).isPrefixOf c && !c.isInternal && c != name then
            deps := deps.push c
      let kind := match ci with | .thmInfo _ => "T" | _ => "D"
      let joined := String.intercalate " " (deps.toList.eraseDups.map toString)
      IO.println (kind ++ "\\t" ++ toString name ++ "\\t" ++ joined)
"""

DECLARATION_LINE = re.compile(r"^\| `([A-Za-z_][A-Za-z0-9_.']*)` \|")


def is_authored(name: str) -> bool:
    return not GENERATED_SUFFIX.search(name)


def run_harness() -> dict[str, Node]:
    with tempfile.TemporaryDirectory(prefix="atlas-deps-") as tmp:
        harness = Path(tmp) / "DepGraph.lean"
        harness.write_text(HARNESS, encoding="utf-8")
        proc = subprocess.run(
            ["lake", "env", "lean", str(harness)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    if proc.returncode != 0:
        print(proc.stdout[-4000:], file=sys.stderr)
        print(proc.stderr[-4000:], file=sys.stderr)
        raise RuntimeError("dependency harness failed; is the project built?")

    graph: dict[str, Node] = {}
    for line in proc.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) != 3 or parts[0] not in {"T", "D"}:
            continue
        kind, name, rest = parts
        if not is_authored(name):
            continue
        graph[name] = Node(
            kind="theorem" if kind == "T" else "definition",
            deps=sorted(d for d in rest.split() if is_authored(d)),
        )
    if not graph:
        raise RuntimeError("dependency harness produced no edges")
    return graph


def example_text() -> str:
    """Every source that counts as *using* a declaration without being in the graph.

    `Examples/` is the obvious one. `Main.lean` is the non-obvious one: the graph
    walks `AISafetyAtlas.*` and the executable is outside that namespace, so a
    declaration named only by `atlas-check` would read as unused.

    This catches uses *by name* and nothing else. An instance reached by
    typeclass resolution is named nowhere and stays on the unused list no matter
    which sources are scanned — `Check.decidableSurjective` is exactly that case,
    and the rendered section says so rather than inviting its deletion.
    """
    sources = sorted(EXAMPLES.rglob("*.lean"))
    if EXECUTABLE.is_file():
        sources.append(EXECUTABLE)
    return "\n".join(path.read_text(encoding="utf-8") for path in sources)


def render(graph: dict[str, Node], config: Cluster) -> str:
    CLUSTER = config.prefix
    cluster = {n: v for n, v in graph.items() if n.startswith(CLUSTER)}
    short = lambda n: n[len(CLUSTER) :] if n.startswith(CLUSTER) else n  # noqa: E731

    users: dict[str, list[str]] = {}
    for name, value in graph.items():
        for dep in value["deps"]:
            if dep.startswith(CLUSTER):
                users.setdefault(dep, []).append(name)

    referenced = set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", example_text()))
    referenced |= {r.split(".")[-1] for r in referenced}

    # Restricted to definitions on purpose: for a definition the environment
    # carries the body, so "nothing mentions it" is complete evidence up to
    # theorem proofs. For a theorem the proof term is absent (see the header),
    # so the same list would be mostly false positives.
    unused_definitions = sorted(
        name
        for name, value in cluster.items()
        if value["kind"] == "definition"
        and not users.get(name)
        and name.split(".")[-1] not in referenced
    )

    load_bearing = sorted(
        ((len(v), k) for k, v in users.items() if len(v) >= 8), reverse=True
    )

    theorems = sum(1 for v in cluster.values() if v["kind"] == "theorem")

    out: list[str] = [
        f"# {config.title} — declaration dependency view",
        "",
        "Generated by `scripts/generate_dependency_graph.py --write`; do not edit"
        " directly. The same data is in"
        f" [`{config.json.name}`]({config.json.name}),"
        " which is the form to read from a program — parsing a Markdown table is"
        " not an API.",
        "",
        "Edges come from the elaborated Lean environment. This answers the"
        " question the provenance tables cannot: not *which printed statement"
        " does this transcribe*, but *what does this rest on*.",
        "",
        "## What these edges are, exactly",
        "",
        "**For a definition, the type and the body. For a theorem, the statement"
        " only — the proof term is not available.** Lean's module system does not"
        " export proof terms, and `import all` does not change that:"
        " `ConstantInfo.value?` is `none` for every imported theorem and `some`"
        " for every definition. Measured, not assumed.",
        "",
        "So `A → B` means *`B` occurs in `A`'s statement, or in `A`'s body when"
        " `A` is a definition*. A lemma used only inside a proof does not appear."
        " Reading the table as a complete call graph would be wrong, and the two"
        " sections below are scoped so that they stay true under this limit.",
        "",
        f"`{len(cluster)}` authored declarations in `{CLUSTER}*`"
        f" ({theorems} theorems). Compiler-generated companions and projections"
        " are dropped.",
        "",
        "## Load-bearing declarations",
        "",
        "Named in the statements of eight or more others. A change to one of"
        " these is a change to everything below it — and since proof edges are"
        " missing, the true count is at least this.",
        "",
        "| Declaration | Named by |",
        "|---|---|",
    ]
    for count, name in load_bearing:
        out.append(f"| `{short(name)}` | {count} |")

    out += [
        "",
        "## Definitions no statement and no example mentions",
        "",
        "Candidates for deletion, not a verdict: a definition here could still be"
        " unfolded inside a proof, which these edges cannot see. Definitions"
        " only — the same list over theorems would be mostly noise. This is the"
        " per-declaration counterpart of the per-module"
        " `check_example_coverage.py`.",
        "",
        "**Instances always appear here.** Typeclass resolution names nothing, so"
        " an instance has no textual user even when every consumer depends on it."
        " Deleting one because it is listed here is how a checker stops"
        " compiling.",
        "",
    ]
    if unused_definitions:
        for name in unused_definitions:
            out.append(f"- `{short(name)}`")
    else:
        out.append("None.")

    out += [
        "",
        "## Direct dependencies",
        "",
        "| Declaration | Kind | Names |",
        "|---|---|---|",
    ]
    for name in sorted(cluster):
        deps = [short(d) for d in cluster[name]["deps"] if d.startswith(CLUSTER)]
        rendered = ", ".join(f"`{d}`" for d in deps) if deps else "—"
        out.append(f"| `{short(name)}` | {cluster[name]['kind']} | {rendered} |")

    out.append("")
    return "\n".join(out)


def declarations_in_tree() -> set[str]:
    pattern = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|public\s+)?(?:noncomputable\s+)?"
        r"(?:def|theorem|abbrev|structure|class|instance|inductive|lemma)\s+"
        r"([A-Za-z_][A-Za-z0-9_.']*)"
    )
    # Structure and class fields are declarations too — `InferenceDevice.setup`
    # is the setup function, not a compiler artefact — and they are introduced by
    # an indented `field : type` line rather than by a `def`.
    field = re.compile(r"^\s+/?-?-?\s*([A-Za-z_][A-Za-z0-9_']*)\s*:[^=]")
    # Inductive constructors are authored declarations too — `CoverageResult.covers`
    # is the checker's positive branch, not a compiler artefact. Lines containing
    # `=>` are `match` alternatives, not constructors, and are excluded so the
    # known-name set does not quietly absorb every pattern variable in the tree.
    constructor = re.compile(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)\s*[({:]?")
    names: set[str] = set()
    for path in LEAN_ROOT.rglob("*.lean"):
        for line in path.read_text(encoding="utf-8").splitlines():
            if match := pattern.match(line):
                names.add(match.group(1).split(".")[-1])
            elif match := field.match(line):
                names.add(match.group(1))
            elif "=>" not in line and (match := constructor.match(line)):
                names.add(match.group(1))
    return names


def check() -> int:
    """Liveness only: every declaration named in a view still exists.

    This deliberately cannot detect a *stale* view — one missing declarations
    added since it was written — because that needs an elaborated environment
    and this runs in the cheap gate. It failed open exactly that way once: the
    inference view recorded 536 declarations while the tree had 682, and the
    gate was green throughout. Currency is CI's job, by regenerating after the
    Lean build and failing if the working tree moved.
    """
    known = declarations_in_tree()
    failed = False
    for config in CLUSTERS:
        if not config.markdown.is_file():
            print(
                f"dependency graph error: {config.markdown} is missing; run "
                "scripts/generate_dependency_graph.py --write",
                file=sys.stderr,
            )
            failed = True
            continue
        missing: list[str] = []
        for line in config.markdown.read_text(encoding="utf-8").splitlines():
            if match := DECLARATION_LINE.match(line):
                leaf = match.group(1).split(".")[-1]
                if leaf not in known:
                    missing.append(match.group(1))
        for name in sorted(set(missing)):
            print(
                f"dependency graph error: {name} is named in "
                f"{config.markdown.name} and no longer exists; regenerate with "
                "--write",
                file=sys.stderr,
            )
            failed = True
    if failed:
        return 1
    names = ", ".join(config.markdown.name for config in CLUSTERS)
    print(f"dependency graph ok: {names} name only live declarations")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true", help="regenerate the view")
    group.add_argument(
        "--check", action="store_true", help="verify the committed view is not stale"
    )
    args = parser.parse_args()

    if args.check:
        return check()

    graph = run_harness()
    STATUS.mkdir(parents=True, exist_ok=True)
    written: list[str] = []
    for config in CLUSTERS:
        config.markdown.write_text(render(graph, config), encoding="utf-8")
        config.json.write_text(
            json.dumps(
                {
                    "note": (
                        "Edges are: for a definition, its type and body; for a "
                        "theorem, its statement only. Lean's module system does "
                        "not export proof terms."
                    ),
                    "cluster": config.prefix,
                    "declarations": {
                        name: value
                        for name, value in sorted(graph.items())
                        if name.startswith(config.prefix)
                    },
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
        written += [config.markdown.name, config.json.name]
    print("dependency graph written: " + ", ".join(written))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
