"""Check that backticked atlas identifiers in Lean docstrings resolve.

A docstring that points at a declaration which does not exist survives every
other validator, because nothing else reads docstrings. The usual cause is a
rename whose prose was not updated. A reader following such a pointer finds
nothing, which is worse than no pointer.

Only names that look like atlas declarations are checked: an identifier
containing an underscore, a CamelCase or lowerCamelCase name, or a dotted name
whose head is `AISafetyAtlas`. Those are the three shapes every declaration on
this branch is named in.

**Known limitation.** A short all-lowercase token with no underscore — `hbound`,
`hle` — is indistinguishable from a proof-local binder, which docstrings do refer
to legitimately, so such names are not checked. Nor is resolution
declaration-level: a name is accepted if it appears anywhere in Lean code,
including as a `have` binder, so a dangling reference survives if it happens to
collide with one. Tightening either would make the check noisy, and a noisy
check gets ignored.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "AISafetyAtlas"

CAMEL_CASE = re.compile(r"^(?:[A-Za-z][A-Za-z0-9']*\.)*[A-Z][A-Za-z0-9']*[a-z][A-Z][A-Za-z0-9']*$")
LOWER_CAMEL = re.compile(r"^[a-z][A-Za-z0-9']*[a-z][A-Z][A-Za-z0-9']*$")
ALL_LOWER = re.compile(r"^[a-z][a-z0-9']*$")
# Head components owned by dependencies, not the atlas.
EXTERNAL_ROOTS = {
    "Set", "Finset", "Nat", "Real", "Function", "Equiv", "PMF", "ZMod", "Measure",
    "Fin", "Prod", "Bool", "Classical", "ENNReal", "Filter", "Fintype", "Mathlib",
    "MeasureTheory", "ProbabilityTheory", "PFR", "GaloisField", "IsUniform",
    "Polynomial", "Finsupp", "List", "Option", "Sigma", "Subtype", "Quotient",
}
BACKTICK_SPAN = re.compile(r"`([^`\n]+)`")
NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.\u2032\u2081-\u2089]*")
# Names legitimately mentioned in prose that are not Lean identifiers of ours:
# tactics, registry fields, and results in other libraries.
EXEMPT = {
    "push_neg", "native_decide", "norm_num", "fun_prop", "simp_all", "field_simp",
    "ai_bridge_status", "scope_delta", "lean_artifact", "root_import",
    "No_Free_Lunch_ML", "qaryEntropy_def",
    # Mathlib lemmas and tactic-local names discussed in prose
    "klDiv_eq_zero_iff", "Finset.sum_fiberwise", "kraft_mcmillan_inequality",
    # cited by a vendored docstring (AISafetyAtlas/Upstream/Debate/Prob/Pmf.lean)
    # as the Mathlib lemma its primed variant restates
    "PMF.pure_apply",
    # gate scripts and source-paper labels
    "validate_current_state", "check_print_axioms", "check_print_axioms.py",
    "Proposition_8",
    # the off-root facade allowlist inside check_print_axioms.py, cited by the
    # module whose presence on it is the thing that needs explaining
    "OFF_ROOT_FACADES",
    # names bound inside a proof, referred to by the surrounding prose
    "sigma_abc", "not_covers",
    # names a docstring deliberately says the atlas does NOT use
    "CausalInnovation", "RespectsCoalition", "RashimonProperty",
    # mathematical notation and Lean/Mathlib names, not atlas declarations
    "max_x", "min_x", "sorryAx", "qaryEntropy", "_root_", "binEntropy",
    "H_open", "H_closed", "argmin_a", "mono'", "implemented_by",
    # tactics and Lean/Mathlib vocabulary discussed in prose
    "sorry", "plausible", "tsum", "decide", "omega", "linarith", "gcongr",
}
DEPS = [
    ROOT / ".lake" / "packages" / "PFR" / "PFR",
]
# Names a docstring cites that a *dependency* owns, listed rather than resolved
# by scanning `.lake`. Scanning made the verdict depend on whether the packages
# happened to be on disk: the cheap gate builds no Lean, so these five citations
# passed on a developer machine and failed in CI, and the reverse -- a misspelled
# dependency name accepted locally -- was equally possible. Listing them makes
# the check deterministic in both environments. `check_dependency_names` below
# verifies the list against the real package whenever it *is* checked out, so it
# cannot rot into a set of names PFR no longer defines.
DEPENDENCY_NAMES = {
    "condEntropy_prod_eq_sum": "PFR",
    "mutual_comp_le": "PFR",
    "mutual_comp_comp_le": "PFR",
    "condMutual_comp_comp_le": "PFR",
}


def known_modules() -> set[str]:
    """Module paths under `AISafetyAtlas/`, plus every declared namespace.

    A qualified reference `AISafetyAtlas.Inference.entropyOn` resolves when
    `AISafetyAtlas.Inference` is a real namespace or module *and* `entropyOn` is
    a real identifier — which rejects a real tail hung under a fictional
    namespace while accepting ordinary qualified prose.
    """
    names = {"AISafetyAtlas"}
    for path in SRC.rglob("*.lean"):
        names.add(".".join(path.relative_to(ROOT).with_suffix("").parts))
        text = path.read_text()
        decls = re.findall(r"^namespace ([A-Za-z_][A-Za-z0-9_'.]*)", text, re.M)
        # structures and classes also open a namespace for their fields
        decls += re.findall(
            r"^(?:@\[[^\]]*\]\s*)?(?:public |private |protected )*"
            r"(?:structure|class|inductive) ([A-Za-z_][A-Za-z0-9_'.]*)", text, re.M)
        for ns in decls:
            parts = ns.split(".")
            parts = ns.split(".")
            for i in range(1, len(parts) + 1):
                names.add(".".join(parts[:i]))
            for base in list(names):
                if base.endswith("." + parts[0]) or base == parts[0]:
                    names.add(base)
    return names


DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:public\s+|private\s+|protected\s+|noncomputable\s+"
    r"|partial\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)")
END_RE = re.compile(r"^end\s*(\S*)\s*$")


def qualified_names() -> tuple[set[str], set[str]]:
    """Every declaration's **full** name, and every atlas module stem.

    The set below is what a consumer can actually type. `code_identifiers` is
    deliberately broad and matches a bare tail anywhere in the tree, which is
    right for catching renames but blind to the failure this pairs with: a name
    qualified by the *module* it lives in rather than by its namespace. Every
    module under `AISafetyAtlas/Control/` declares `namespace AISafetyAtlas.
    Control`, so `RequisiteVariety.ashby_variety_ge` reads like a qualified name
    and resolves nowhere, while a tail-only test accepts it for as long as
    `ashby_variety_ge` exists anywhere.

    Namespaces are tracked with a stack rather than a regex over the file,
    because `end` closes sections too and a name's namespace is whatever is open
    where it is declared.
    """
    full: set[str] = set()
    stems: set[str] = set()
    modules: set[str] = set()
    # Every component of every declared namespace. A module stem that is also a
    # namespace component — `Objective`, `Corruption`, `Computability` — can
    # legitimately head a qualified name, and its tail may be a structure field
    # this parser does not collect. Only a stem that names **no** namespace is
    # unambiguously a module qualifier.
    namespace_parts: set[str] = set()
    for path in SRC.rglob("*.lean"):
        parts = path.relative_to(ROOT).with_suffix("").parts
        modules.add(".".join(parts))
        # directories are importable prefixes in prose even without a .lean
        for i in range(1, len(parts)):
            modules.add(".".join(parts[:i]))
        stems.add(path.stem)
        stack: list[str] = []
        for line in path.read_text(encoding="utf-8").splitlines():
            opened = NAMESPACE_RE.match(line)
            if opened:
                stack.append(opened.group(1))
                namespace_parts.update(opened.group(1).split("."))
                continue
            closed = END_RE.match(line)
            if closed:
                if stack and (
                    closed.group(1) in {"", stack[-1]} or stack[-1].endswith(closed.group(1))
                ):
                    stack.pop()
                continue
            declared = DECL_RE.match(line)
            if declared:
                prefix = ".".join(stack)
                full.add(f"{prefix}.{declared.group(1)}" if prefix else declared.group(1))
    resolvable = set()
    for name in full | modules:
        pieces = name.split(".")
        for i in range(len(pieces)):
            resolvable.add(".".join(pieces[i:]))
    return resolvable, (stems - EXTERNAL_ROOTS) - namespace_parts


def code_identifiers() -> set[str]:
    """Every identifier token that appears in Lean *code* across the atlas.

    Deliberately broad. The failure this catches is a docstring naming something
    that exists nowhere — a rename whose prose was not updated. Requiring the
    name to be a top-level declaration would also flag structure fields,
    namespaces and constructors, which are legitimate things for prose to name,
    so the bar is "appears in the source at all".
    """
    names: set[str] = set(DEPENDENCY_NAMES)
    paths = list(SRC.rglob("*.lean"))
    paths.append(ROOT / "AISafetyAtlas.lean")  # the root module, where imports live
    for path in paths:
        code = re.sub(r"/-[-!]?.*?-/", " ", path.read_text(), flags=re.S)
        code = re.sub(r"--[^\n]*", " ", code)
        names.update(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", code))
        # also register each dotted suffix, so `Namespace.thm` matches `thm`
        for m in re.findall(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+", code):
            parts = m.split(".")
            for i in range(len(parts)):
                names.add(".".join(parts[i:]))
    return names


# Hand-written prose a consumer reads before ever opening a Lean file. Generated
# views under docs/status/ are excluded: they are regenerated, not edited, and a
# name is fixed at its source.
PROSE = ["README.md", "STATE.md", "docs/guide", "docs/provenance", "docs/bridges"]
# Filenames look exactly like qualified names. `Stochastic.lean` names a file,
# `.v` and `.thy` name other provers' sources, and none of them is a Lean name.
FILE_SUFFIXES = (
    ".lean", ".md", ".py", ".yaml", ".yml", ".json", ".toml", ".sh", ".txt",
    ".v", ".thy", ".agda", ".rs", ".hs", ".cff", ".html",
)


def prose_files() -> list[Path]:
    found: list[Path] = []
    for entry in PROSE:
        target = ROOT / entry
        if target.is_file():
            found.append(target)
        elif target.is_dir():
            found.extend(sorted(target.rglob("*.md")))
    return found


def module_qualified(text: str, rel: Path, resolvable: set[str], stems: set[str]) -> list[str]:
    """Flag `Module.declaration` in prose, the one rule worth applying here.

    Only this rule, not the full identifier resolution the Lean pass runs.
    Documentation legitimately names things that are not atlas declarations —
    other provers' lemmas, paper theorem numbers, fields of a reader's own
    model — and flagging those would make the check noisy enough to ignore. A
    module-qualified name is different: it is unambiguously a name a reader will
    type and fail to resolve, which is exactly the failure that put twenty
    untypeable entries in `AISafetyAtlas.Control`'s table and three more in this
    README while both passed every check in the gate.
    """
    problems: list[str] = []
    for line0, line in enumerate(text.splitlines(), 1):
        for span in BACKTICK_SPAN.finditer(line):
            inner = span.group(1).strip()
            if "/" in inner or inner.endswith(FILE_SUFFIXES):
                continue
            for m in NAME_RE.finditer(inner):
                name = m.group(0)
                if name in EXEMPT or not all(name.split(".")):
                    continue
                if "." not in name or name.split(".")[0] not in stems:
                    continue
                if name in resolvable:
                    continue
                problems.append(
                    f"{rel}:{line0}: `{name}` is qualified by a module, not a "
                    "namespace, so a reader cannot type it"
                )
    return problems


# A primary-surface row: `| **Role** | `name` | …`. Only these are checked for
# reachability. Prose is not, and must not be: `AISafetyAtlas.Control`'s
# blocked-consumer table names `trueReturn` and `History` precisely because they
# are *out* of reach, and `AISafetyAtlas.SelfAwareness` says in as many words that
# no declaration below uses `Knowable`. Naming what a module cannot reach is the
# point of those passages. A surface table makes the opposite promise.
SURFACE_ROW = re.compile(r"^\|\s*\*\*[^|]+\*\*\s*\|\s*`([^`]+)`")


def reachable_modules(module: str) -> set[str]:
    seen: set[str] = set()
    pending = [module]
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        path = ROOT / Path(current.replace(".", "/") + ".lean")
        if not path.is_file():
            continue
        for imported in re.findall(r"^public import (\S+)", path.read_text(), re.M):
            if imported.startswith("AISafetyAtlas"):
                pending.append(imported)
    return seen


def declaring_modules() -> dict[str, set[str]]:
    owners: dict[str, set[str]] = {}
    for path in SRC.rglob("*.lean"):
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        for line in path.read_text(encoding="utf-8").splitlines():
            declared = DECL_RE.match(line)
            if declared:
                owners.setdefault(declared.group(1).split(".")[-1], set()).add(module)
    return owners


def unreachable_surface(owners: dict[str, set[str]]) -> list[str]:
    """Surface rows naming a declaration the module cannot deliver.

    A reader imports a module, reads its table, copies a row, and gets `unknown
    identifier` — the name being perfectly correct and declared in a sibling the
    module does not import. `AISafetyAtlas.Preference` and
    `AISafetyAtlas.Verification` are peers of their nested modules rather than
    facades over them, so their rows carry an `Import` column naming what a
    reader needs. This keeps that honest.
    """
    problems: list[str] = []
    for path in sorted(SRC.glob("*.lean")):
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        within = reachable_modules(module)
        text = path.read_text(encoding="utf-8")
        for line0, line in enumerate(text.splitlines(), 1):
            row = SURFACE_ROW.match(line)
            if not row:
                continue
            tail = row.group(1).split(".")[-1]
            if tail not in owners or owners[tail] & within:
                continue
            if re.search(r"\|\s*`?\.[A-Za-z]", line) or "this module" in line:
                continue  # the row names the import a reader needs
            problems.append(
                f"{path.relative_to(ROOT)}:{line0}: surface row `{row.group(1)}` is "
                f"declared in {sorted(owners[tail])[0]}, which this module does not "
                "import — name the import in the row or import it"
            )
    return problems


def docstring_spans(text: str):
    """Yield (offset, body) for each `/-- … -/` and `/-! … -/` block."""
    for m in re.finditer(r"/-[-!](.*?)-/", text, re.S):
        yield m.start(), m.group(1)


def check_dependency_names() -> list[str]:
    """Confirm each `DEPENDENCY_NAMES` entry is real, when the package is present.

    Absent, this is a no-op and the listed names are trusted, which is what keeps
    the cheap gate honest without a Lean checkout. Present, every entry has to
    appear in the package's own sources, so a dependency bump that renames one is
    caught here rather than leaving a docstring pointing at nothing.
    """
    problems: list[str] = []
    for root in DEPS:
        if not root.exists():
            continue
        package = root.name
        wanted = {n for n, owner in DEPENDENCY_NAMES.items() if owner == package}
        if not wanted:
            continue
        found: set[str] = set()
        for path in root.rglob("*.lean"):
            text = path.read_text()
            found.update(n for n in wanted if n in text)
        for missing in sorted(wanted - found):
            problems.append(
                f"DEPENDENCY_NAMES: `{missing}` is listed as a {package} name but "
                f"appears nowhere in {package}; the docstring citing it is stale"
            )
    return problems


def main() -> int:
    known = code_identifiers()
    modules = known_modules()
    resolvable, stems = qualified_names()
    # names that resolve outside the atlas: anything Mathlib/PFR defines is not
    # our business, so only flag names that look atlas-shaped and are unknown
    problems: list[str] = []
    for path in sorted(SRC.rglob("*.lean")):
        text = path.read_text()
        rel = path.relative_to(ROOT)
        for offset, body in docstring_spans(text):
            line0 = text.count("\n", 0, offset) + 1
            for span in BACKTICK_SPAN.finditer(body):
              inner = span.group(1).strip()
              if "/" in inner or inner.endswith((".md", ".lean", ".py", ".txt", ".yaml")):
                continue  # a file path, not an identifier
              if re.fullmatch(r"[0-9a-f]{16,}", inner):
                continue  # a commit hash or digest
              solo = NAME_RE.fullmatch(inner) is not None
              for m in NAME_RE.finditer(inner):
                name = m.group(0)
                if name in EXEMPT:
                    continue
                if name.startswith("AISafetyAtlas."):
                    # a real tail under a fictional namespace is not a resolution
                    prefix, _, tail = name.rpartition(".")
                    prefix_ok = prefix in modules or prefix.split(".")[-1] in modules
                    # `resolvable` is the exact test; the older prefix/tail pair
                    # accepted a real tail hung under a real *module*, which is
                    # the defect this now catches.
                    if name in resolvable:
                        continue
                    if name in known or name in modules or (prefix_ok and tail in known):
                        problems.append(
                            f"{rel}:~{line0}: `{name}` is qualified by a module, not a "
                            "namespace, so it resolves nowhere — use the name a "
                            "consumer can type"
                        )
                        continue
                    problems.append(
                        f"{rel}:~{line0}: `{name}` is neither a declaration nor a module"
                    )
                    continue
                # A name qualified by an atlas *module* is not a Lean name.
                # Checked before the tail fallback below, which would otherwise
                # accept it on the strength of its last component alone.
                head = name.split(".")[0]
                # `Preference.` ending a sentence is prose, not a qualified name
                dotted = "." in name and all(name.split("."))
                if dotted and head in stems and name not in resolvable:
                    problems.append(
                        f"{rel}:~{line0}: `{name}` is qualified by a module, not a "
                        "namespace, so it resolves nowhere — use the name a "
                        "consumer can type"
                    )
                    continue
                if name in known or name.split(".")[-1] in known:
                    continue
                looks_atlas = (
                    ("_" in name and len(name) > 4)
                    # CamelCase and lowerCamelCase: the two shapes every
                    # definition and theorem on this branch is named in
                    or (CAMEL_CASE.match(name) and name.split(".")[0] not in EXTERNAL_ROOTS)
                    or (LOWER_CAMEL.match(name) and len(name) > 6)
                    # plain lowercase words of declaration length: `volume`,
                    # `histogram`, `nonadaptive`, `errs`, `fano` are all real
                    # declarations of exactly this shape
                    # a plain lowercase word, but only when it is the whole
                    # span: `volume`, `histogram`, `nonadaptive`, `errs` and
                    # `fano` are real declarations of exactly this shape, while
                    # a lowercase word inside a longer span is ordinary prose
                    or (solo and ALL_LOWER.match(name) and len(name) >= 4)
                )
                if looks_atlas:
                    problems.append(f"{rel}:~{line0}: `{name}` appears nowhere in the atlas sources")

    problems.extend(unreachable_surface(declaring_modules()))
    problems.extend(check_dependency_names())

    prose = 0
    for path in prose_files():
        prose += 1
        problems.extend(
            module_qualified(
                path.read_text(encoding="utf-8"),
                path.relative_to(ROOT),
                resolvable,
                stems,
            )
        )

    if problems:
        for p in problems:
            print(f"check_docstring_identifiers: {p}", file=sys.stderr)
        print(
            f"check_docstring_identifiers: {len(problems)} unresolved identifier(s) in docstrings",
            file=sys.stderr,
        )
        return 1
    print(
        "docstring identifiers ok: every atlas-shaped backticked name resolves, "
        f"and no module-qualified name in {prose} hand-written prose files"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
