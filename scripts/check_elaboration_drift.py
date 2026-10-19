#!/usr/bin/env python3
"""Compare declarations by their *elaborated type*, not by their source text.

`check_statement_drift.py` compares what the source says. That is the right
check for almost everything and it is blind to one case, which is the case a
toolchain migration is most likely to produce:

    theorem foo : Fintype.card α = n := ...

Unchanged, character for character, in both trees. If upstream renamed a class
behind an `alias`, or changed which instance resolution picks, or made a
definition reducible where it was not, this text now means something different.
No text diff sees it. `axiom-audit` does not see it -- the proof is still a
proof, of a different statement. A build canary does not see it -- it compiles.
`check_public_api.py` does not see it -- the name is unchanged.

So this walks the elaborated environment and fingerprints each declaration's
**type expression**: the constants it mentions, the instances resolution
actually chose, the universe structure, the binder kinds. Two trees agree here
only if the two statements mean the same thing to the kernel.

Two decisions in here are load-bearing.

*Lean emits, Python hashes.* The harness prints a normalized rendering of the
`Expr` and this script hashes it with `hashlib`. Hashing inside Lean with
`String.hash` would be shorter, and would also compare a v4.31 hash against a
v4.33 hash computed by a different implementation of the hash -- every
declaration would look changed, and the check would be worthless in exactly the
situation it exists for.

*Binder names out, binder kinds in.* Renaming a bound variable changes nothing
and would be noise. Changing `{x : α}` to `[x : α]` changes resolution and is
signal.

The interesting output is not "the fingerprint changed" on its own. It is a
declaration whose **printed type is identical and whose fingerprint is not**:
that is the silent case above, and this script reports it separately.

Dumps are written `--raw`, which keeps the normal form itself rather than a
digest of it. A hashed dump can say that a statement moved; only a raw one can
say *which constants moved in it*, which is what `--classify` adjudicates
against `docs/status/elaboration-classes.json`. Hashing would save bytes in the
working tree and would cost the one result a reader most wants to re-derive.

Usage:
    # on each tree, once
    python3 scripts/check_elaboration_drift.py --dump docs/status/elab-baseline-v4310.json --raw
    python3 scripts/check_elaboration_drift.py --dump docs/status/elab-baseline-v4330.json --raw

    # then, needing neither tree
    python3 scripts/check_elaboration_drift.py --compare old.json new.json

    # which substitution classes account for the silent set
    python3 scripts/check_elaboration_drift.py --classify old.json new.json

    # the standing check on an ordinary branch: dump this tree and hold it to the
    # recorded baseline, where only a silent change is a failure. --pp-against
    # prints only what that comparison reads; the dump is then no baseline.
    python3 scripts/check_elaboration_drift.py --dump current.json --raw \
        --pp-against docs/status/elab-baseline-v4330.json
    python3 scripts/check_elaboration_drift.py --compare \
        docs/status/elab-baseline-v4330.json current.json --fatal silent
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "AISafetyAtlas"

# The standing verdicts, keyed by the upstream constant whose disappearance
# identifies a substitution. Adjudicating a class once and recording it here is
# what keeps the human cost of a toolchain bump proportional to how much
# *upstream* churned rather than to how large this library has become.
CLASSES_PATH = ROOT / "docs" / "status" / "elaboration-classes.json"

# Silent changes ruled on one declaration at a time. A class excuses an upstream
# substitution wherever it recurs; an edit inside this library that changes the
# meaning of statements nobody edited (a definition re-encoded, a structure
# given new arguments) has no class, and policy says each such change needs its
# own verdict. An entry pins both fingerprints by digest, so it excuses exactly
# the change that was read and nothing that comes after it.
ACCEPTED_PATH = ROOT / "docs" / "status" / "elaboration-accepted.json"

MARK_BEGIN = "ATLAS-ELAB-BEGIN"
MARK_END = "ATLAS-ELAB-END"
SEP = "\t"

PRIVATE_RE = re.compile(r"^_private\.(?P<module>[^.].*?)\.\d+\.(?P<name>.+)$")

# Structural constants the compiler emits for every inductive. Their types track
# the toolchain's own encoding choices, so a change there says nothing about
# whether *our* statements moved.
NOT_SOURCE_KINDS = frozenset({"constructor", "recursor", "quot"})


def _built_modules(root: Path) -> list[str]:
    """Modules under `root` that have a compiled artifact and a source file."""
    build = root / ".lake" / "build" / "lib" / "lean" / PREFIX
    modules = [PREFIX] if (build.parent / f"{PREFIX}.olean").is_file() else []
    modules += [
        name
        for path in sorted(build.rglob("*.olean"))
        for name in [
            f"{PREFIX}." + str(path.relative_to(build)).removesuffix(".olean").replace("/", ".")
        ]
        if (root / (name.replace(".", "/") + ".lean")).is_file()
    ]
    return modules


def built_modules(root: Path | None = None) -> list[str]:
    """Every atlas module with a compiled artifact, each named explicitly.

    Same discovery rule as `check_drift_coverage.py`, and for the same reason:
    `import all` is transitive for constants but not for declaration ranges, so
    importing only the root would leave most of the tree without the range that
    tells a hand-written declaration from a generated one.

    A module is ours when it has both a compiled artifact and a source. Lake does
    not prune build output for a source that no longer exists, and a restored
    build cache carries those orphans across a rename or a consolidation; they
    fail to load with "incompatible header", which reads as a broken tree rather
    than as the stale artifact it is. Requiring the artifact keeps the property
    above; requiring the source drops the orphans, and the two together are the
    modules this tree actually compiles.
    """
    return _built_modules(root or ROOT)


# The normalizer, shared by the sweep and by `--self-test` so that what the
# self-test validates is the encoding the sweep actually uses. The rendering is
# deliberately verbose and deliberately not pretty: it exists to be compared byte
# for byte across two Lean versions, so every choice in it is about stability
# rather than legibility.
NORMALIZER = [
    "open Lean Lean.Meta in",
    "private def atlasBi : BinderInfo → String",
    '  | .default => "d"',
    '  | .implicit => "i"',
    '  | .strictImplicit => "s"',
    '  | .instImplicit => "c"',
    "",
    # Universe parameters are rendered by their position in the declaration's own
    # `levelParams`, so renaming `u` to `u_1` upstream is not mistaken for a
    # change in meaning.
    "open Lean in",
    "private partial def atlasLvl (ps : List (Name × Nat)) : Level → String",
    '  | .zero => "0"',
    '  | .succ l => s!"(S {atlasLvl ps l})"',
    '  | .max a b => s!"(M {atlasLvl ps a} {atlasLvl ps b})"',
    '  | .imax a b => s!"(I {atlasLvl ps a} {atlasLvl ps b})"',
    "  | .param n => match ps.lookup n with",
    '    | some i => s!"#{i}"',
    '    | none => s!"?{n}"',
    '  | .mvar _ => "?m"',
    "",
    # Each distinct subterm is rendered once per declaration and reused. A
    # type is a DAG, and the rendering writes every shared subterm out in full:
    # the largest fingerprints run to megabytes, 92 MB over the tree, and
    # walking every copy was most of the sweep. The rendering of a subterm does
    # not depend on where it sits -- bound variables are de Bruijn indices -- so
    # reusing it cannot change a byte of the output.
    "open Lean in",
    "private partial def atlasFpM (ps : List (Name × Nat)) (e : Expr) :",
    "    StateM (Std.HashMap Expr String) String := do",
    "  if let some r := (← get).get? e then return r",
    "  let r ← match e with",
    # Bound variables are de Bruijn indices already, so binder *names* never
    # reach the rendering and renaming one is invisible here. Binder *kinds* do
    # reach it: `{x : α}` and `[x : α]` resolve differently and must not agree.
    '    | .bvar i => pure s!"(b {i})"',
    '    | .fvar _ => pure "(fv)"',
    '    | .mvar _ => pure "(mv)"',
    '    | .sort l => pure s!"(s {atlasLvl ps l})"',
    "    | .const n ls =>",
    '        pure s!"(c {n} [{String.intercalate "," (ls.map (atlasLvl ps))}])"',
    '    | .app f a => return s!"(@ {← atlasFpM ps f} {← atlasFpM ps a})"',
    "    | .lam _ t b bi =>",
    '        return s!"(L {atlasBi bi} {← atlasFpM ps t} {← atlasFpM ps b})"',
    "    | .forallE _ t b bi =>",
    '        return s!"(F {atlasBi bi} {← atlasFpM ps t} {← atlasFpM ps b})"',
    "    | .letE _ t v b _ =>",
    '        return s!"(E {← atlasFpM ps t} {← atlasFpM ps v} {← atlasFpM ps b})"',
    '    | .lit (.natVal n) => pure s!"(n {n})"',
    '    | .lit (.strVal s) => pure s!"(t {s})"',
    '    | .proj n i x => return s!"(p {n} {i} {← atlasFpM ps x})"',
    # `mdata` carries elaborator bookkeeping, never meaning.
    "    | .mdata _ x => atlasFpM ps x",
    "  modify (·.insert e r)",
    "  return r",
    "",
    "open Lean in",
    "private def atlasFp (ps : List (Name × Nat)) (e : Expr) : String :=",
    "  (atlasFpM ps e).run' {}",
    "",
]


def _lean_strings(values: list[str]) -> str:
    return "#[" + ", ".join(json.dumps(v, ensure_ascii=False) for v in values) + "]"


def harness_source(
    modules: list[str],
    *,
    select: list[str] | None = None,
    fp: bool | str = True,
    pp: bool | set[str] = True,
    only: set[str] | None = None,
) -> str:
    """A `run_cmd` printing a normalized rendering of every atlas type.

    `select` keeps only declarations compiled into those modules, which is how a
    shard of a parallel sweep reports its own modules and nothing it merely
    imports. `fp=False` skips the fingerprint, `fp="generated"` computes it for
    compiler-generated declarations only, and `pp` limits the printed form
    to the named declarations (full names); `only` emits rows for the named
    declarations alone, for the second pass.
    """
    imports = [f"import all {module}" for module in modules]
    select_check = (
        [f"    unless {_lean_strings(select)}.contains m do", "      continue"]
        if select is not None
        else []
    )
    only_check = (
        [f'    unless {_lean_strings(sorted(only))}.contains s!"{{n}}" do', "      continue"]
        if only is not None
        else []
    )
    if fp == "generated":
        fp_line = '    let fp := if generated then atlasFp ps ci.type else ""'
    else:
        fp_line = "    let fp := atlasFp ps ci.type" if fp else '    let fp := ""'
    if pp is True:
        pp_gate = []
    elif pp is False:
        pp_gate = ["    let wantPp := false"]
    else:
        pp_gate = [f'    let wantPp := {_lean_strings(sorted(pp))}.contains s!"{{n}}"']
    return "\n".join(
        [
            "module",
            *imports,
            "import Lean",
            "",
            "/-! Generated harness for scripts/check_elaboration_drift.py. -/",
            "",
            *NORMALIZER,
            "open Lean Lean.Meta in",
            "run_cmd Lean.Elab.Command.liftTermElabM do",
            "  let env ← Lean.getEnv",
            "  let mut rows : Array String := #[]",
            "  for (n, ci) in env.constants.toList do",
            "    if n.isInternalDetail || n.hasMacroScopes then continue",
            # Select by the module a declaration was compiled into, never by its
            # name. Filtering on the `AISafetyAtlas` name prefix skipped 636
            # declarations that live in our modules under someone else's
            # namespace -- the whole vendored `Kolmogorov.*` layer, including
            # `Kolmogorov.FormalSystem.chaitinIncompleteness`, which a graded
            # theorem in `AISafetyAtlas.Logic` is assigned from. They compile
            # here, we ship them, and a silent change in one of them reaches our
            # statements.
            # `findModuleOf?`, not `Environment.getModuleFor?`: the latter does
            # not exist at v4.31.0, and this script has to elaborate on the tree
            # it is comparing against as well as on the current one.
            "    let m := match ← Lean.findModuleOf? n with",
            '      | some mod => s!"{mod}"',
            '      | none => ""',
            f'    unless m.startsWith "{PREFIX}." || m == "{PREFIX}" do',
            "      continue",
            *select_check,
            *only_check,
            "    let kind :=",
            "      match ci with",
            '      | .thmInfo _ => "theorem"',
            '      | .axiomInfo _ => "axiom"',
            '      | .inductInfo _ => "inductive"',
            '      | .ctorInfo _ => "constructor"',
            '      | .recInfo _ => "recursor"',
            '      | .opaqueInfo _ => "opaque"',
            '      | .quotInfo _ => "quot"',
            '      | .defnInfo _ => "def"',
            "    let structural :=",
            "      env.isProjectionFn n || isAuxRecursor env n",
            "        || isRecCore env n || isNoConfusion env n",
            "    let range ← Lean.findDeclarationRanges? n",
            "    let generated := structural || range.isNone",
            "    let ps := ci.levelParams.zipIdx",
            fp_line,
            # Printed only so a human reading a reported difference can see what
            # moved. The verdict is never taken from this string.
            *pp_gate,
            "    let pp ← (do",
            *(["      if !wantPp then return \"\""] if pp_gate else []),
            "      try",
            "        let f ← Lean.Meta.ppExpr ci.type",
            '        pure ((toString f).replace "\\n" " ")',
            '      catch _ => pure "<pp failed>")',
            "    rows := rows.push",
            f'      s!"{{n}}{SEP}{{kind}}{SEP}{{m}}{SEP}{{generated}}{SEP}{{fp}}{SEP}{{pp}}"',
            f'  IO.println "{MARK_BEGIN}"',
            "  for r in rows.qsort (· < ·) do IO.println r",
            f'  IO.println "{MARK_END}"',
            "",
        ]
    )


SELFTEST_NS = "AtlasElabSelfTest"

# Known-answer cases for `--self-test`. Each pair names two declarations and
# whether their fingerprints must agree. `axiom` throughout: only types are
# fingerprinted, so proving any of these would test nothing and cost a build.
SELFTEST_CASES = [
    (
        "renameA",
        "renameB",
        True,
        "binder and universe-parameter names are noise and must not register",
    ),
    (
        "kindImplicit",
        "kindInstance",
        False,
        "{x : α} and [x : α] resolve differently and must not agree",
    ),
    (
        "silentP",
        "silentQ",
        False,
        "the silent case: identical printed type, different instance chosen",
    ),
    ("differentA", "differentB", False, "genuinely different statements must differ"),
]


def selftest_source() -> str:
    """A file whose answers are known in advance, to check the encoding itself.

    A fingerprint that never changes and a fingerprint that always changes are
    both useless, and a cross-version comparison cannot tell you which one you
    built -- by the time you run it, you have nothing to check the answer
    against. So the encoding gets validated here, on one toolchain, against
    cases whose verdicts are decided by hand.
    """
    return "\n".join(
        [
            "import Mathlib.Data.Fintype.Card",
            "import Lean",
            "",
            "/-! Generated self-test for scripts/check_elaboration_drift.py. -/",
            "",
            *NORMALIZER,
            f"namespace {SELFTEST_NS}",
            "",
            "axiom renameA : ∀ {α : Type u} (x : α), x = x",
            "axiom renameB : ∀ {β : Type v} (y : β), y = y",
            "",
            "axiom kindImplicit : ∀ {α : Type} {_i : Inhabited α}, True",
            "axiom kindInstance : ∀ {α : Type} [_i : Inhabited α], True",
            "",
            # Two instances on the same type, definitionally equal and named
            # apart. `Fintype.card`'s instance argument is instance-implicit, so
            # the pretty printer hides it and both statements print the same.
            "def SelfT : Type := Bool",
            "def instP : Fintype SelfT := inferInstanceAs (Fintype Bool)",
            "def instQ : Fintype SelfT := inferInstanceAs (Fintype Bool)",
            "axiom silentP : @Fintype.card SelfT instP = 2",
            "axiom silentQ : @Fintype.card SelfT instQ = 2",
            "",
            "axiom differentA : ∀ (n : Nat), n + 0 = n",
            "axiom differentB : ∀ (n : Nat), 0 + n = n",
            "",
            f"end {SELFTEST_NS}",
            "",
            "open Lean Lean.Meta in",
            "run_cmd Lean.Elab.Command.liftTermElabM do",
            "  let env ← Lean.getEnv",
            f'  IO.println "{MARK_BEGIN}"',
            "  for n in env.constants.toList.map Prod.fst do",
            f"    unless (`{SELFTEST_NS}).isPrefixOf n do continue",
            "    match env.find? n with",
            "    | none => pure ()",
            "    | some ci =>",
            "      let fp := atlasFp ci.levelParams.zipIdx ci.type",
            "      let f ← Lean.Meta.ppExpr ci.type",
            '      let pp := (toString f).replace "\\n" " "',
            f'      IO.println s!"{{n}}{SEP}{{fp}}{SEP}{{pp}}"',
            f'  IO.println "{MARK_END}"',
            "",
        ]
    )


def do_selftest() -> int:
    with tempfile.TemporaryDirectory(prefix="atlas-elab-selftest-") as tmp:
        path = Path(tmp) / "ElabSelfTest.lean"
        path.write_text(selftest_source(), encoding="utf-8")
        proc = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    blob = (proc.stdout or "") + "\n" + (proc.stderr or "")
    if proc.returncode != 0 or MARK_BEGIN not in blob:
        print(blob[-4000:], file=sys.stderr)
        print(f"check_elaboration_drift: self-test did not run (exit {proc.returncode})",
              file=sys.stderr)
        return 1

    body = blob.split(MARK_BEGIN, 1)[1].split(MARK_END, 1)[0]
    seen: dict[str, tuple[str, str]] = {}
    for line in body.splitlines():
        parts = line.split(SEP)
        if len(parts) == 3:
            seen[parts[0].removeprefix(f"{SELFTEST_NS}.")] = (parts[1], parts[2])

    failures = 0
    for left, right, want_equal, why in SELFTEST_CASES:
        if left not in seen or right not in seen:
            print(f"  ? {left} vs {right}: not elaborated", file=sys.stderr)
            failures += 1
            continue
        (left_fp, left_pp), (right_fp, right_pp) = seen[left], seen[right]
        if (left_fp == right_fp) != want_equal:
            verb = "differ but must agree" if want_equal else "agree but must differ"
            print(f"  x {left} vs {right}: fingerprints {verb} -- {why}", file=sys.stderr)
            failures += 1
            continue
        print(f"  . {left} vs {right}: {why}")
        # The silent case is only a demonstration if the printed forms really are
        # indistinguishable; if the pretty printer started showing the instance,
        # this case would be passing for an uninteresting reason.
        if left == "silentP" and left_pp != right_pp:
            print(
                f"  x {left} vs {right}: printed types differ, so this no longer "
                f"exercises the silent case\n      {left_pp}\n      {right_pp}",
                file=sys.stderr,
            )
            failures += 1

    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if failures:
        print(f"check_elaboration_drift: {failures} self-test failure(s) at {toolchain}",
              file=sys.stderr)
        return 1
    print(f"check_elaboration_drift: self-test passed at {toolchain}")
    return 0


def source_name(name: str) -> str:
    """`_private.M.0.helper` is written `helper`; the digit is a build detail."""
    match = PRIVATE_RE.match(name)
    return match.group("name") if match else name


def _run_harness(source: str) -> list[list[str]]:
    """Elaborate one harness and return its rows, split into their six fields."""
    with tempfile.TemporaryDirectory(prefix="atlas-elab-drift-") as tmp:
        harness = Path(tmp) / "ElabDrift.lean"
        harness.write_text(source, encoding="utf-8")
        proc = subprocess.run(
            ["lake", "env", "lean", str(harness)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    blob = (proc.stdout or "") + "\n" + (proc.stderr or "")
    if proc.returncode != 0 or MARK_BEGIN not in blob:
        print(blob[-4000:], file=sys.stderr)
        print(f"check_elaboration_drift: lean failed (exit {proc.returncode})", file=sys.stderr)
        raise SystemExit(1)
    body = blob.split(MARK_BEGIN, 1)[1].split(MARK_END, 1)[0]
    return [parts for line in body.splitlines() if line.strip()
            for parts in [line.split(SEP)] if len(parts) == 6]


def drift_jobs(modules: int) -> int:
    """How many harnesses run at once: ATLAS_DRIFT_JOBS, else what memory allows.

    Each shard imports the closure of its own modules, which peaked near 3.7 GB
    for the whole tree, so the default budgets ATLAS_DRIFT_GB_PER_JOB (5) each
    against available memory, capped at the core count and the module count.
    """
    if os.environ.get("ATLAS_DRIFT_JOBS"):
        return max(1, int(os.environ["ATLAS_DRIFT_JOBS"]))
    try:
        with open("/proc/meminfo", encoding="utf-8") as meminfo:
            avail_kb = next(int(line.split()[1]) for line in meminfo
                            if line.startswith("MemAvailable:"))
    except (OSError, StopIteration, ValueError):
        return 1
    per_job = float(os.environ.get("ATLAS_DRIFT_GB_PER_JOB", "5"))
    return max(1, min(int(avail_kb / 1048576 / per_job), os.cpu_count() or 1, modules))


def _shards(modules: list[str], count: int) -> list[list[str]]:
    """Split modules into `count` shards of similar compiled size.

    Largest first, each to the currently lightest shard. The olean size stands
    in for how much there is to fingerprint, so one shard does not end up
    holding every large module and finishing long after the rest.
    """
    lib = ROOT / ".lake" / "build" / "lib" / "lean"

    def size(module: str) -> int:
        path = lib / (module.replace(".", "/") + ".olean")
        return path.stat().st_size if path.is_file() else 0

    shards: list[list[str]] = [[] for _ in range(count)]
    loads = [0] * count
    for module in sorted(modules, key=size, reverse=True):
        lightest = loads.index(min(loads))
        shards[lightest].append(module)
        loads[lightest] += size(module) + 1  # + 1: unsized modules still spread
    return [shard for shard in shards if shard]


def elaborate(
    modules: list[str],
    raw: bool = False,
    *,
    pp: bool | set[str] = True,
    jobs: int = 1,
) -> tuple[dict[str, dict], dict[str, str], set[str]]:
    """Fingerprint every declaration the modules compile.

    Returns the declarations by key, each key's full Lean name, and the full
    names more than one shard reported. Those are constants Lean creates on
    demand -- a `congr_simp` lemma is realized in whichever module first needs
    it, so two modules can each hold one. A single environment keeps one copy;
    which one is the full environment's business, so the caller re-reads these
    from it rather than guessing. With
    `jobs > 1` the modules are split into shards elaborated in parallel, each
    importing only its own modules and reporting only declarations compiled
    into them. A fingerprint is a rendering of the stored type, so which other
    modules a shard happens to load cannot change it.
    """
    if jobs > 1 and len(modules) > 1:
        from concurrent.futures import ThreadPoolExecutor

        shards = _shards(modules, min(jobs, len(modules)))
        with ThreadPoolExecutor(max_workers=len(shards)) as pool:
            parts = pool.map(
                lambda shard: _run_harness(harness_source(shard, select=shard, pp=pp)),
                shards,
            )
            rows = [row for part in parts for row in part]
    else:
        rows = _run_harness(harness_source(modules, pp=pp))

    out: dict[str, dict] = {}
    names: dict[str, str] = {}
    duplicated: set[str] = set()
    for name, kind, module, generated, fp, pp_text in rows:
        key = source_name(name)
        if key in out and names[key] == name and out[key]["module"] != module:
            duplicated.add(name)
            continue
        # `source_name` drops the module qualification from a private name, and
        # the modules now in scope contain declarations called `Alice`, `Bob` and
        # `Comp`. Two declarations sharing a key would silently overwrite one
        # another and the loss would look like a clean comparison.
        if key in out and out[key]["module"] != module:
            print(
                f"check_elaboration_drift: {key} names declarations in both "
                f"{out[key]['module']} and {module}; the key is not unique",
                file=sys.stderr,
            )
            raise SystemExit(1)
        out[key] = {
            "kind": kind,
            "module": module,
            "generated": generated.strip() == "true",
            # Hashed here, in Python, so the digest does not depend on which
            # Lean version produced the rendering.
            "fp": fp if raw else hashlib.sha256(fp.encode("utf-8")).hexdigest()[:32],
            "pp": pp_text,
        }
        names[key] = name
    if not out:
        print("check_elaboration_drift: harness produced no rows", file=sys.stderr)
        raise SystemExit(1)
    return out, names, duplicated


def full_environment_rows(modules: list[str], printed: bool | set[str]) -> dict[str, list[str]]:
    """Every atlas row from one environment of every module, as a single sweep has it.

    Two things need that environment. The printed form depends on which
    notations and delaborators are in scope -- a later module can add notation
    for an earlier definition, so printing with fewer modules loaded could make
    a silent change look visible, the one error this check must not make. And a
    constant Lean creates on demand (a `congr_simp` lemma, realized in whichever
    module first needs it) can sit in several modules; one environment keeps one
    copy, a shard keeps whichever of its own it met first, and only this
    environment says which copy a single sweep reports. Such constants have no
    source position, so they are always `generated`, and their fingerprints are
    taken from here.
    """
    rows = _run_harness(harness_source(modules, fp="generated", pp=printed))
    return {row[0]: row for row in rows}


def _comparable_fp(fp: str, raw: bool) -> str:
    return hashlib.sha256(fp.encode("utf-8")).hexdigest()[:32] if raw else fp


def git(*args: str) -> str:
    proc = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, check=False)
    return proc.stdout.strip() if proc.returncode == 0 else ""


def read_dump(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def fp_digest(fp: str) -> str:
    """The digest an accepted-verdict entry records for a raw fingerprint."""
    return hashlib.sha256(fp.encode("utf-8")).hexdigest()


def split_accepted(
    silent: list[str],
    old_decls: dict[str, dict],
    new_decls: dict[str, dict],
    accepted_path: Path = ACCEPTED_PATH,
) -> tuple[list[str], list[str]]:
    """Split a silent set into the changes a recorded verdict covers and the rest.

    A declaration is covered only when its name is recorded and **both** digests
    match: the baseline fingerprint the verdict was read against and the
    fingerprint it accepted. A later change to the same declaration therefore
    stays silent and fails. Entries are matched against raw fingerprints; a
    hashed dump's fingerprint is already a digest, matches nothing here, and so
    fails closed.
    """
    if not accepted_path.is_file():
        return [], list(silent)
    registry = json.loads(accepted_path.read_text(encoding="utf-8"))
    pinned = {
        entry["name"]: (entry["baseline"], entry["current"])
        for verdict in registry["verdicts"]
        for entry in verdict["declarations"]
    }
    covered: list[str] = []
    remaining: list[str] = []
    for name in silent:
        digests = (fp_digest(old_decls[name]["fp"]), fp_digest(new_decls[name]["fp"]))
        (covered if pinned.get(name) == digests else remaining).append(name)
    return covered, remaining


def write_dump(path: Path, payload: dict) -> None:
    """A dump, as plain text.

    These files are read by `--compare` and `--classify` and by nothing else --
    not by a person, not by another script -- so the obvious move is to compress
    them, and it was the wrong one. Measured on the two sides of this migration:

        plaintext, two commits, after `git gc`:  391,190 bytes
        gzipped,   two commits, after `git gc`:  734,042 bytes

    Git already zlib-compresses every blob and deltas each dump against the one
    before it. Handing it a `.gz` defeats both, and the repository pays for that
    once per migration forever. What compression was actually bought for was the
    42,000-line diff, and `.gitattributes` gives that away for free: `-diff`
    renders the change as one `Bin` line while the bytes stay delta-compressible.
    """
    text = json.dumps(payload, indent=1, sort_keys=True) + "\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def do_dump(
    path: Path,
    raw: bool = False,
    only_reaching: list[str] | None = None,
    pp_against: Path | None = None,
) -> int:
    modules = built_modules()
    if not modules:
        print(
            "check_elaboration_drift: no compiled modules under "
            f"{(ROOT / '.lake/build/lib/lean' / PREFIX)}; run `lake build` first",
            file=sys.stderr,
        )
        return 1
    # A scoped dump elaborates only the modules a moved dependency can reach
    # (`dependency_reach.py`). It records that scope, so `--compare` holds the
    # baseline to the same modules instead of reporting the rest as removed.
    scope: dict | None = None
    if only_reaching:
        from dependency_reach import reach

        scoped, reason = reach(only_reaching, modules)
        print(f"check_elaboration_drift: {reason}")
        if scoped is not None:
            modules = scoped
            scope = {"packages": sorted(only_reaching), "modules": scoped}
    # Two passes. The first fingerprints in parallel and prints nothing; the
    # second prints, in one process over every module, only what needs a
    # printed form. Without `pp_against` that is everything, which is what a
    # baseline needs. With it, it is the declarations whose fingerprint differs
    # from that baseline's -- the only ones `--compare` reads a printed form
    # for (silent against visible) -- and usually there are none.
    #
    # A scoped dump keeps the single sweep it always was: it imports only the
    # reaching modules and reports what they transitively bring in, which a
    # set of shards would not reproduce, and it is small enough not to need
    # the speed.
    declarations: dict[str, dict] = {}
    if modules and scope is not None:
        declarations, _, _ = elaborate(modules, raw=raw)
    elif modules:
        jobs = drift_jobs(len(modules))
        print(f"check_elaboration_drift: fingerprinting {len(modules)} module(s), {jobs} at once")
        declarations, names, duplicated = elaborate(modules, raw=raw, pp=False, jobs=jobs)
        if pp_against is None:
            wanted = None  # a baseline: print everything, as a full sweep does
        else:
            baseline = read_dump(pp_against)
            base_raw = bool(baseline.get("raw"))
            wanted = {
                names[key]
                for key, entry in declarations.items()
                if key in baseline["declarations"]
                and _comparable_fp(baseline["declarations"][key]["fp"], base_raw and not raw)
                != _comparable_fp(entry["fp"], raw and not base_raw)
            }
        print(
            "check_elaboration_drift: reading the full environment, printing "
            + ("every declaration" if wanted is None else f"{len(wanted)} declaration(s)")
        )
        rows = full_environment_rows(modules, True if wanted is None else wanted)
        mismatched = []
        absent: list[str] = []
        for key, entry in declarations.items():
            row = rows.get(names[key])
            if row is None:
                # An on-demand constant a shard realized in one of our modules
                # can also sit in an upstream module, whose copy the full
                # environment keeps; a single sweep then never reports it, so
                # neither does this. A hand-written declaration cannot do that.
                if entry["generated"]:
                    absent.append(key)
                else:
                    mismatched.append(f"{key} (absent from the full environment)")
                continue
            _, kind, module, generated, fp, pp_text = row
            entry["pp"] = pp_text
            if generated.strip() == "true":
                entry.update(
                    kind=kind,
                    module=module,
                    generated=True,
                    fp=fp if raw else hashlib.sha256(fp.encode("utf-8")).hexdigest()[:32],
                )
            elif (kind, module) != (entry["kind"], entry["module"]) or entry["generated"]:
                mismatched.append(f"{key} ({entry['module']} in its shard, {module} in full)")
        # A hand-written declaration lives in exactly one module, so the shard
        # and the full environment must agree on it. If they do not, the
        # parallel sweep is not the sweep it replaces; say so and stop.
        if mismatched:
            for line in mismatched[:20]:
                print(f"check_elaboration_drift: shard disagrees: {line}", file=sys.stderr)
            return 1
        for key in absent:
            del declarations[key]
        extra = set(rows) - set(names.values())
        if extra:
            print(
                f"check_elaboration_drift: {len(extra)} declaration(s) in the full "
                f"environment and in no shard, e.g. {sorted(extra)[:3]}",
                file=sys.stderr,
            )
            return 1
    payload = {
        "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "commit": git("rev-parse", "HEAD"),
        "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "modules": len(modules),
        "raw": raw,
        # Which declarations the sweep looked at. A dump written before this key
        # existed selected by name prefix and so is missing everything our
        # modules compile under someone else's namespace; comparing it against a
        # module-selected dump reports those as additions, which they are not.
        "selector": "module",
        "declarations": declarations,
    }
    if pp_against is not None and scope is None:
        # Printed forms are present only where the fingerprint moved. A dump
        # like this can be compared against its baseline and can never serve
        # as one: unchanged declarations carry an empty printed form.
        payload["printed"] = f"changed against {pp_against}"
    if scope is not None:
        payload["scope"] = scope
    write_dump(path, payload)
    print(
        f"check_elaboration_drift: wrote {len(declarations)} declaration(s) from "
        f"{len(modules)} module(s) at {payload['toolchain']} to {path}"
    )
    return 0


def classify(old_decls: dict[str, dict], new_decls: dict[str, dict]) -> dict[str, list[str]]:
    """Sort every declaration into the thing a reviewer would do about it.

    The split that matters is `silent` from `visible`. Both are meaning changes;
    only the first is one a person reading the diff could not have caught, so it
    is the one worth spending review on first.

    Compiler-generated declarations get their own bucket rather than being
    dropped. Their types encode the toolchain's own choices, so a change there is
    expected on a version move and says nothing about our statements -- but a
    *large* change there is still worth seeing, and silently discarding it would
    make this the second checker in this repository to under-report by filtering.
    """
    shared = set(old_decls) & set(new_decls)
    out: dict[str, list[str]] = {
        "added": [],
        "removed": [],
        "added_generated": [],
        "removed_generated": [],
        "silent": [],
        "visible": [],
        "generated": [],
    }
    # A declaration that appears or vanishes is only news when we wrote it. The
    # v4.31 -> v4.33 move retired eighteen `enumList*` lemmas that Mathlib's
    # `Fintype` deriving handler had emitted into our namespace; reporting those
    # next to a genuinely deleted theorem would make the first real one easy to
    # miss.
    for names, source, derived in (
        (sorted(set(new_decls) - set(old_decls)), "added", "added_generated"),
        (sorted(set(old_decls) - set(new_decls)), "removed", "removed_generated"),
    ):
        side = new_decls if source == "added" else old_decls
        for name in names:
            out[derived if side[name]["generated"] else source].append(name)
    for name in sorted(shared):
        before, after = old_decls[name], new_decls[name]
        if before["fp"] == after["fp"]:
            continue
        if after["kind"] in NOT_SOURCE_KINDS or (before["generated"] and after["generated"]):
            out["generated"].append(name)
        elif before["pp"] == after["pp"]:
            out["silent"].append(name)
        else:
            out["visible"].append(name)
    return out


def divergence(before: str, after: str, window: int = 90) -> str | None:
    """Where two normal forms first part company, with a little context.

    A hashed dump cannot answer "what moved", only "something moved", and a
    reviewer holding 131 names and no reasons cannot adjudicate any of them. So
    `--dump --raw` keeps the normal form itself, and this locates the first
    position at which the two disagree. It is a *pointer*, not a verdict: one
    upstream argument-order change shifts every position after it, so the first
    divergence is the thing to look at, not the whole story.
    """
    if before == after:
        return None
    limit = min(len(before), len(after))
    at = next((i for i in range(limit) if before[i] != after[i]), limit)
    start = max(0, at - window // 3)
    return (
        f"was: ...{before[start:at + window]}...\n"
        f"      now: ...{after[start:at + window]}..."
    )


CONSTANT_RE = re.compile(r"\(c ([^ ]+) \[")


def substitution(before: str, after: str) -> tuple[set[str], set[str]]:
    """Which constants a statement stopped mentioning, and which it started."""
    old_constants = set(CONSTANT_RE.findall(before))
    new_constants = set(CONSTANT_RE.findall(after))
    return old_constants - new_constants, new_constants - old_constants


def account(
    gone: set[str], came: set[str], classes: dict[str, dict]
) -> tuple[list[str], set[str], set[str]]:
    """Which classes fire on this substitution, and what they fail to explain.

    A class fires when everything its `removes` names actually left. Firing is
    not the verdict: the caller classifies a declaration only when the classes
    that fired account for **both** sides, so the returned leftovers must both
    be empty.

    Checking the departure alone is unsound. `setOf` leaving would match the
    `setOf` class no matter what replaced it, so `setOf -> Evil` would certify
    clean and an unrelated substitution riding along in the same statement would
    be swallowed whole. The class is a claim about a replacement; a check that
    never looks at the replacement is not checking the claim.

    `adds` is a containment rather than an equality because a constant the
    substitution introduces may already occur in the statement for some other
    reason, and then it is not a new arrival at all -- the `Set` subset class
    adds `LE.le`, and two of the declarations it covers were already saying
    `LE.le` elsewhere. That direction is the safe one: it can only leave an
    arrival unexplained, which fails closed.
    """
    fired = [key for key, entry in classes.items() if set(entry["removes"]) <= gone]
    explained_gone = {name for key in fired for name in classes[key]["removes"]}
    explained_came = {name for key in fired for name in classes[key]["adds"]}
    return fired, gone - explained_gone, came - explained_came


def do_classify(old_path: Path, new_path: Path, show: int) -> int:
    """Group the silent set by substitution class and report only what is new.

    A migration produces silent changes in proportion to how much of this library
    touches whatever upstream renamed, so the count grows as the library does:
    131 at 5358 declarations, 171 at 5994. The number of *reasons* does not --
    those come from upstream's churn, and there were eleven. Reading 171 names is
    work that grows without bound; reading the two that belong to a class nobody
    has ruled on yet is work that stays the same size.

    So each class is adjudicated once, recorded in `docs/status/elaboration-
    classes.json` against an anchor that holds at both toolchains, and never
    re-litigated. This exits non-zero when something is left over, which is the
    only state that needs a person.
    """
    old, new = read_dump(old_path), read_dump(new_path)
    if _refuse_partial_baseline(old, old_path):
        return 2
    if not (old.get("raw") and new.get("raw")):
        print(
            "check_elaboration_drift: --classify needs dumps written with --raw; a "
            "hashed dump says that a statement moved and not which constants moved in "
            "it, and the class is a claim about the constants.",
            file=sys.stderr,
        )
        return 1

    registry = json.loads(CLASSES_PATH.read_text(encoding="utf-8"))
    classes = {entry["key"]: entry for entry in registry["classes"]}

    old_decls, new_decls = old["declarations"], new["declarations"]
    silent = classify(old_decls, new_decls)["silent"]

    counts: collections.Counter[str] = collections.Counter()
    unclassified: list[tuple[str, list[str], list[str]]] = []
    # Same constants in a different arrangement: no substitution to name, so the
    # shape of the statement moved -- a binder kind, an argument order, a
    # universe. Nothing in the registry can ever excuse one of these, and they are
    # reported apart from the unclassified so they cannot be waved through as a
    # missing entry.
    rearranged: list[str] = []
    for name in silent:
        gone, came = substitution(old_decls[name]["fp"], new_decls[name]["fp"])
        if not gone and not came:
            rearranged.append(name)
            continue
        fired, left_gone, left_came = account(gone, came, classes)
        if fired and not left_gone and not left_came:
            counts.update(fired)
        else:
            unclassified.append((name, sorted(left_gone), sorted(left_came)))

    print(
        f"elaboration classes: {old['toolchain']} ({old['commit'][:12]}) -> "
        f"{new['toolchain']} ({new['commit'][:12]})"
    )
    print(f"  {len(silent)} silent change(s), {len(counts)} known class(es) recurred")
    for key, hits in counts.most_common():
        print(f"  . {hits:4d}  {classes[key]['change']}")
    for key, entry in classes.items():
        if key not in counts:
            print(f"       0  {entry['change']} (recorded, not seen here)")

    if rearranged:
        print(
            f"\n{len(rearranged)} silent change(s) kept every constant and rearranged them.\n"
            "No substitution class can account for this: a binder kind, an argument\n"
            "order or a universe moved, and each one needs its own verdict."
        )
        for name in rearranged[:show]:
            print(f"  x {name}")
            print(f"      {divergence(old_decls[name]['fp'], new_decls[name]['fp'])}")

    if unclassified:
        print(
            f"\n{len(unclassified)} silent change(s) no recorded class accounts for. Listed\n"
            "below is what is left over after every class that fired: constants that\n"
            "left with no class naming them, and constants that arrived with no class\n"
            "predicting them. Either side being non-empty is enough -- a class excuses a\n"
            "*replacement*, so a departure it names does not license whatever took the\n"
            "place. Adjudicate each against a fact that holds at both toolchains, record\n"
            f"it in {CLASSES_PATH.relative_to(ROOT)}, and the next migration will not ask."
        )
        for name, gone, came in unclassified[:show]:
            print(f"  ? {name}")
            print(f"      unexplained left: {' '.join(gone) or '-'}")
            print(f"      unexplained new:  {' '.join(came) or '-'}")
        if len(unclassified) > show:
            print(f"  ... and {len(unclassified) - show} more")

    if rearranged or unclassified:
        return 1
    print("\ncheck_elaboration_drift: every silent change belongs to an adjudicated class")
    return 0


def _refuse_partial_baseline(old: dict, old_path: Path) -> bool:
    """A dump written with --pp-against has no printed form for most entries.

    As the old side of a comparison every unchanged-print declaration would
    read as visibly changed, and a silent one would hide among them.
    """
    if "printed" not in old:
        return False
    print(
        f"check_elaboration_drift: {old_path} has printed forms only where the "
        f"fingerprint moved ({old['printed']}); write a baseline without --pp-against",
        file=sys.stderr,
    )
    return True


def do_compare(
    old_path: Path,
    new_path: Path,
    show: int,
    fatal: str = "any",
    accepted_path: Path = ACCEPTED_PATH,
) -> int:
    old = read_dump(old_path)
    new = read_dump(new_path)
    if _refuse_partial_baseline(old, old_path):
        return 2
    old_decls, new_decls = old["declarations"], new["declarations"]

    # A scoped dump looked at the modules a moved dependency reaches and nothing
    # else; outside them the dependency cannot have changed anything, so the
    # baseline is held to the same modules.
    scope = new.get("scope")
    if scope is not None:
        in_scope = set(scope["modules"])
        old_decls = {name: entry for name, entry in old_decls.items() if entry.get("module") in in_scope}
        print(
            f"check_elaboration_drift: scoped to {len(in_scope)} module(s) reaching "
            f"{', '.join(scope['packages'])}"
        )
        if not in_scope:
            print(
                "check_elaboration_drift: no atlas module imports the moved package, "
                "so it cannot have changed the meaning of any statement here"
            )
            return 0

    old_selector, new_selector = old.get("selector", "name"), new.get("selector", "name")
    if old_selector != new_selector:
        print(
            f"check_elaboration_drift: {old_path.name} selected declarations by "
            f"{old_selector} and {new_path.name} by {new_selector}. The two sweeps did "
            "not look at the same set, so what follows counts the difference between "
            "the selectors as well as the difference between the trees; anything the "
            "narrower sweep never saw appears here as an addition.\n",
            file=sys.stderr,
        )

    buckets = classify(old_decls, new_decls)
    added, removed = buckets["added"], buckets["removed"]
    silent, visible, generated = buckets["silent"], buckets["visible"], buckets["generated"]
    accepted, silent = split_accepted(silent, old_decls, new_decls, accepted_path)
    shared = set(old_decls) & set(new_decls)

    print(
        f"elaboration drift: {old['toolchain']} ({old['commit'][:12]}) -> "
        f"{new['toolchain']} ({new['commit'][:12]})"
    )
    derived_moved = len(buckets["added_generated"]) + len(buckets["removed_generated"])
    print(
        f"  {len(shared)} declaration(s) in both, {len(added)} added, {len(removed)} removed"
    )
    print(f"  {len(silent)} changed meaning with an IDENTICAL printed type")
    if accepted:
        print(
            f"  {len(accepted)} more did so and are covered by a recorded verdict "
            f"({accepted_path.name})"
        )
    print(f"  {len(visible)} changed with a visibly different type")
    print(
        f"  {len(generated)} compiler-generated changed and {derived_moved} appeared or "
        "vanished (expected on a toolchain move)"
    )

    if silent:
        print(
            "\nSame printed type, different elaborated type. This is the case no text\n"
            "diff, axiom audit or build can see; each one needs a human verdict."
        )
        explained = old.get("raw") and new.get("raw")
        for name in silent[:show]:
            print(f"  ! {name}")
            print(f"      {new_decls[name]['pp'][:200]}")
            if explained:
                where = divergence(old_decls[name]["fp"], new_decls[name]["fp"])
                if where:
                    print(f"      {where}")
        if len(silent) > show:
            print(f"  ... and {len(silent) - show} more")

    if visible:
        print("\nType changed and the change is visible in the printed form:")
        for name in visible[:show]:
            print(f"  ~ {name}")
            print(f"      was: {old_decls[name]['pp'][:160]}")
            print(f"      now: {new_decls[name]['pp'][:160]}")
        if len(visible) > show:
            print(f"  ... and {len(visible) - show} more")

    for label, names in (
        ("removed", removed),
        ("added", added),
        ("removed, compiler-generated", buckets["removed_generated"]),
        ("added, compiler-generated", buckets["added_generated"]),
    ):
        if names:
            print(f"\n{label} ({len(names)}):")
            for name in names[:show]:
                print(f"  {name}")
            if len(names) > show:
                print(f"  ... and {len(names) - show} more")

    if fatal == "silent":
        # `silent` is the only bucket this policy reads, so an empty comparison
        # satisfies it exactly as a clean one does. A dump taken against the
        # wrong tree, or written by a selector that shares no key with the
        # baseline, would otherwise report success for having examined nothing.
        if not shared:
            print(
                f"\ncheck_elaboration_drift: {old_path.name} and {new_path.name} share "
                "no declaration, so this comparison examined nothing",
                file=sys.stderr,
            )
            return 1
        if silent:
            return 1
        print(
            f"\ncheck_elaboration_drift: nothing changed meaning behind an unchanged "
            f"printed type, across {len(shared)} declaration(s) compared"
        )
        return 0
    return 1 if (silent or visible or added or removed) else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dump", type=Path, help="elaborate this tree and write a fingerprint file")
    parser.add_argument(
        "--compare", nargs=2, type=Path, metavar=("OLD", "NEW"), help="compare two fingerprint files"
    )
    parser.add_argument(
        "--classify",
        nargs=2,
        type=Path,
        metavar=("OLD", "NEW"),
        help="group the silent set of two --raw dumps by adjudicated substitution "
        "class, and report only what no class accounts for (the committed dumps "
        "are raw, so this reproduces the recorded result)",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="check the fingerprint encoding against known-answer cases on this toolchain",
    )
    parser.add_argument(
        "--raw",
        action="store_true",
        help="with --dump, keep the normal form instead of its digest, so a later "
        "--compare can say what moved and not only that something did (large)",
    )
    parser.add_argument(
        "--only-reaching",
        metavar="PACKAGES",
        help="with --dump, elaborate only the modules whose imports reach these "
        "comma-separated packages (a scoped dependency move; see dependency_reach.py). "
        "Falls back to every module when Mathlib carries one of them",
    )
    parser.add_argument(
        "--pp-against",
        type=Path,
        metavar="BASELINE",
        help="with --dump, print types only where the fingerprint differs from "
        "BASELINE -- all --compare against it reads -- instead of printing every "
        "declaration; the dump cannot then serve as a baseline itself",
    )
    parser.add_argument("--show", type=int, default=20, help="how many names to list per section")
    parser.add_argument(
        "--fatal",
        choices=("any", "silent"),
        default="any",
        help="with --compare, which findings set the exit status. `any` asks the "
        "migration question -- did anything move at all. `silent` asks the one an "
        "ordinary branch can be held to: adding, removing or visibly editing a "
        "statement is that branch's work, but an unchanged printed type cannot "
        "change meaning through an edit, so a silent change is never something the "
        "branch asked for",
    )
    arguments = parser.parse_args()

    chosen = sum(
        map(bool, (arguments.dump, arguments.compare, arguments.classify, arguments.self_test))
    )
    if chosen != 1:
        parser.error("give exactly one of --dump, --compare, --classify or --self-test")
    if arguments.only_reaching and not arguments.dump:
        parser.error("--only-reaching only means anything with --dump")
    if arguments.pp_against and not arguments.dump:
        parser.error("--pp-against only means anything with --dump")
    if arguments.raw and not arguments.dump:
        parser.error("--raw only means anything with --dump")
    if arguments.fatal != "any" and not arguments.compare:
        parser.error("--fatal only means anything with --compare")
    if arguments.self_test:
        return do_selftest()
    if arguments.dump:
        only = [name for name in (arguments.only_reaching or "").split(",") if name]
        return do_dump(
            arguments.dump,
            raw=arguments.raw,
            only_reaching=only or None,
            pp_against=arguments.pp_against,
        )
    if arguments.classify:
        return do_classify(arguments.classify[0], arguments.classify[1], arguments.show)
    return do_compare(arguments.compare[0], arguments.compare[1], arguments.show, arguments.fatal)


if __name__ == "__main__":
    sys.exit(main())
