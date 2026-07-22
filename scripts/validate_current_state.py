#!/usr/bin/env python3
"""Validate timeless repository invariants for ordinary development and CI."""

from __future__ import annotations

import os
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "AISafetyAtlas.lean"
LEAN_BUILD_TARGETS = ROOT / "scripts/lean_build_targets.txt"
FORBIDDEN_LEAN_TOKEN = re.compile(
    r"\b(sorry|admit|axiom|sorryAx|native_decide|implemented_by)\b"
)
IMPORT_LINE = re.compile(r"^\s*(?:public\s+)?import\s+(.+)$", re.MULTILINE)
LOCAL_MODULE = re.compile(r"^AISafetyAtlas(?:\.[A-Za-z_][A-Za-z0-9_]*)*$")


def require(condition: bool, message: str) -> None:
    if not condition:
        print(f"current-state validation error: {message}", file=sys.stderr)
        raise SystemExit(1)


def read_version(path: Path, pattern: str, label: str) -> str:
    match = re.search(pattern, path.read_text(encoding="utf-8"))
    require(match is not None, f"could not read version from {label}")
    return match.group(1)


def lean_code_without_comments_or_strings(source: str) -> str:
    """Mask Lean comments and strings while preserving token boundaries."""
    masked: list[str] = []
    index = 0
    block_comment_depth = 0

    while index < len(source):
        if block_comment_depth:
            if source.startswith("/-", index):
                masked.extend("  ")
                block_comment_depth += 1
                index += 2
            elif source.startswith("-/", index):
                masked.extend("  ")
                block_comment_depth -= 1
                index += 2
            else:
                masked.append("\n" if source[index] == "\n" else " ")
                index += 1
            continue

        if source.startswith("--", index):
            line_end = source.find("\n", index)
            if line_end == -1:
                masked.extend(" " * (len(source) - index))
                break
            masked.extend(" " * (line_end - index))
            masked.append("\n")
            index = line_end + 1
            continue

        if source.startswith("/-", index):
            masked.extend("  ")
            block_comment_depth = 1
            index += 2
            continue

        if source[index] == '"':
            masked.append(" ")
            index += 1
            while index < len(source):
                if source[index] == "\\" and index + 1 < len(source):
                    masked.extend("  ")
                    index += 2
                elif source[index] == '"':
                    masked.append(" ")
                    index += 1
                    break
                else:
                    masked.append("\n" if source[index] == "\n" else " ")
                    index += 1
            continue

        masked.append(source[index])
        index += 1

    return "".join(masked)


def forbidden_lean_tokens(source: str) -> list[str]:
    code = lean_code_without_comments_or_strings(source)
    return [match.group(1) for match in FORBIDDEN_LEAN_TOKEN.finditer(code)]


def lean_module_name(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def local_imports(source: str, local_modules: set[str]) -> set[str]:
    code = lean_code_without_comments_or_strings(source)
    imports: set[str] = set()
    for match in IMPORT_LINE.finditer(code):
        imports.update(
            token for token in match.group(1).split() if token in local_modules
        )
    return imports


def dependency_closure(root: str, graph: dict[str, set[str]]) -> set[str]:
    closure: set[str] = set()
    pending = [root]
    while pending:
        module = pending.pop()
        if module in closure:
            continue
        closure.add(module)
        pending.extend(graph.get(module, set()) - closure)
    return closure


def explicit_lean_build_targets() -> list[str]:
    return [
        line.strip()
        for line in LEAN_BUILD_TARGETS.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]


def validate_scanner_examples() -> None:
    forbidden_examples = [
        "theorem x : True := by sorry",
        "theorem x : True := by\n  exact sorry",
        "theorem x : True := by\n  have h : True := by sorry\n  exact h",
        "private axiom hidden : False",
        "theorem x : True := by admit",
        "theorem x : True := sorryAx True true",
        "example : 1 = 1 := by native_decide",
        "@[implemented_by runtimeValue] opaque proofValue : True",
    ]
    allowed_examples = [
        "-- sorry, sorryAx, native_decide, and axiom are documentation here",
        "/- outer /- nested axiom -/ sorryAx implemented_by -/ "
        "theorem x : True := by trivial",
        'def message := "sorry and native_decide are text, not proofs"',
    ]
    require(
        all(forbidden_lean_tokens(example) for example in forbidden_examples),
        "incomplete-proof scanner does not reject all adversarial examples",
    )
    require(
        not any(forbidden_lean_tokens(example) for example in allowed_examples),
        "incomplete-proof scanner rejects comments or strings",
    )
    require(
        dependency_closure("Atlas", {"Atlas": {"Public"}, "Public": {"Core"}})
        == {"Atlas", "Public", "Core"},
        "Lean import-closure traversal failed its self-test",
    )


def validate_lean_build_closure(lean_files: list[Path]) -> None:
    modules = {lean_module_name(path): path for path in lean_files}
    require("AISafetyAtlas" in modules, "public Lean root module is missing")

    graph = {
        module: local_imports(path.read_text(encoding="utf-8"), set(modules))
        for module, path in modules.items()
    }
    root_closure = dependency_closure("AISafetyAtlas", graph)
    targets = explicit_lean_build_targets()
    require(targets, "Lean build-target manifest is empty")
    require(len(targets) == len(set(targets)), "Lean build-target manifest has duplicates")
    require(
        all(LOCAL_MODULE.fullmatch(target) for target in targets),
        "Lean build-target manifest contains an invalid module name",
    )
    unknown_targets = sorted(set(targets) - set(modules))
    require(not unknown_targets, f"Lean build-target manifest names missing modules: {unknown_targets}")

    uncovered = sorted(set(modules) - root_closure - set(targets))
    require(
        not uncovered,
        "Lean modules are neither reachable from AISafetyAtlas nor explicit CI "
        f"build targets: {uncovered}",
    )

    workflow = (ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8")
    require(
        "xargs lake build < scripts/lean_build_targets.txt" in workflow,
        "CI does not consume the checked Lean build-target manifest",
    )


def main() -> None:
    validate_scanner_examples()

    required_files = [
        "README.md",
        "CONTRIBUTING.md",
        "CITATION.cff",
        "SECURITY.md",
        "LICENSE",
        "STATE.md",
        "registry.yaml",
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
        "AISafetyAtlas.lean",
        "AISafetyAtlas/Computability.lean",
        "AISafetyAtlas/Logic.lean",
        "AISafetyAtlas/Upstream/Attribution/Trilemma.lean",
        "AISafetyAtlas/Explainability.lean",
        "AISafetyAtlas/SocialChoice.lean",
        "AISafetyAtlas/SocialChoice/Utility.lean",
        "AISafetyAtlas/Verification.lean",
        "AISafetyAtlas/Examples/PublicAPI.lean",
        "AISafetyAtlas/Examples/Registry.lean",
        "AISafetyAtlas/Examples/Robot.lean",
        "AISafetyAtlas/Verification/Robot.lean",
        "AISafetyAtlas/Upstream/Arrow.lean",
        "AISafetyAtlas/Survey/BrcicYampolskiy/HaltingExample.lean",
        "docs/README.md",
        "docs/guide/methodology.md",
        "docs/guide/open-work.md",
        "docs/guide/logic-incompleteness.md",
        "docs/guide/contributor-tasks.md",
        "docs/guide/robot-verification-model.md",
        "docs/guide/related-literature.md",
        "docs/status/formalization-status.md",
        "docs/status/atlas-index.md",
        "docs/status/landscape-index.md",
        "docs/status/paper-coverage.md",
        "docs/agent/INDEX.md",
        "docs/agent/by-id.json",
        "docs/agent/search-summary.json",
        "docs/provenance/external-formalizations.md",
        "docs/provenance/formalization-search.json",
        "docs/provenance/formalization-search.md",
        "docs/bridges/ct3-robot-review-package.md",
        "docs/bridges/review-by-012-agentbehavior.md",
        "docs/releases/v0.1.md",
        "docs/releases/v0.2.md",
        "reviews/README.md",
        "scripts/check_docs_paths.py",
        "scripts/agent_gate.sh",
        "landscape.yaml",
        "scripts/generate_registry_views.py",
        "scripts/validate_landscape.py",
        "scripts/check_print_axioms.py",
        "scripts/lean_build_targets.txt",
        "scripts/update_formalization_search.py",
        "scripts/reproduce_isabelle.sh",
        "scripts/reproduce_vnm.sh",
        "scripts/reproduce_chaitin.sh",
        "scripts/reproduce_foundation.sh",
        "AISafetyAtlas/Logic.lean",
        "AISafetyAtlas/Verification/AgentBehavior.lean",
        "AISafetyAtlas/Upstream/Attribution/Trilemma.lean",
        "AISafetyAtlas/Upstream/LICENSE-NOTICE",
        "AISafetyAtlas/Upstream/LICENSE",
        "AISafetyAtlas/Upstream/KolmogorovMathlib/LICENSE",
        "AISafetyAtlas/Upstream/Attribution/LICENSE",
        "AISafetyAtlas/Explainability.lean",
        "AISafetyAtlas/Upstream/KolmogorovMathlib/README.md",
        ".github/CODEOWNERS",
        ".github/ISSUE_TEMPLATE/config.yml",
        ".github/ISSUE_TEMPLATE/formalization-proposal.yml",
        ".github/ISSUE_TEMPLATE/problem-report.yml",
        ".github/pull_request_template.md",
        ".github/workflows/ci.yml",
    ]
    missing = [path for path in required_files if not (ROOT / path).is_file()]
    require(not missing, f"missing required files: {missing}")

    license_text = (ROOT / "LICENSE").read_text(encoding="utf-8")
    require(
        "Apache License" in license_text and "Version 2.0" in license_text,
        "LICENSE is not Apache-2.0",
    )

    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    normalized_readme = " ".join(readme.lower().split())
    require(
        "does not by itself establish" in normalized_readme,
        "mandatory machine-checking disclaimer is missing",
    )

    lean_files = list((ROOT / "AISafetyAtlas").rglob("*.lean"))
    lean_files.append(LEAN_ROOT)
    validate_lean_build_closure(lean_files)
    offenders = {}
    for path in lean_files:
        tokens = forbidden_lean_tokens(path.read_text(encoding="utf-8"))
        if tokens:
            offenders[str(path.relative_to(ROOT))] = tokens
    require(
        not offenders,
        f"released Lean files contain incomplete proof tokens: {offenders}",
    )

    executable_scripts = [
        "scripts/reproduce_isabelle.sh",
        "scripts/reproduce_vnm.sh",
        "scripts/reproduce_chaitin.sh",
        "scripts/reproduce_foundation.sh",
    ]
    nonexecutable = [
        path for path in executable_scripts if not os.access(ROOT / path, os.X_OK)
    ]
    require(not nonexecutable, f"reproduction scripts are not executable: {nonexecutable}")

    # R7-1: STATE.md must embed the generated registry snapshot markers.
    state_text = (ROOT / "STATE.md").read_text(encoding="utf-8")
    require(
        "<!-- BEGIN GENERATED REGISTRY SNAPSHOT -->" in state_text
        and "<!-- END GENERATED REGISTRY SNAPSHOT -->" in state_text,
        "STATE.md must contain generated registry snapshot markers",
    )
    require(
        "<!-- BEGIN GENERATED RELEASE STATUS -->" in state_text
        and "<!-- END GENERATED RELEASE STATUS -->" in state_text,
        "STATE.md must contain generated release-status markers",
    )
    # Release/version coherence: lakefile, CITATION, and the matching release note
    # must agree. Deterministic and offline, so version identifiers cannot drift
    # apart the way the hand-maintained v0.2/v0.3 publication prose once did.
    lake_version = read_version(
        ROOT / "lakefile.toml", r'(?m)^\s*version\s*=\s*"([^"]+)"', "lakefile.toml"
    )
    citation_version = read_version(
        ROOT / "CITATION.cff", r'(?m)^\s*version\s*:\s*"?([^"\s]+)"?', "CITATION.cff"
    )
    require(
        lake_version == citation_version,
        "package version mismatch: "
        f"lakefile.toml {lake_version!r} != CITATION.cff {citation_version!r}",
    )
    # Release notes follow the major.minor convention (v0.1, v0.2, v0.3); the
    # package version carries a patch component (0.3.0). Match on the series.
    minor_series = ".".join(lake_version.split(".")[:2])
    require(
        (ROOT / f"docs/releases/v{minor_series}.md").is_file(),
        f"missing release note docs/releases/v{minor_series}.md "
        f"for package version {lake_version}",
    )
    # Landscape root-import surface must stay dual-listed (R6-3).
    require(
        (ROOT / "landscape.yaml").is_file(),
        "landscape.yaml missing",
    )

    print(
        "current state ok: required public files, Apache-2.0, disclaimer, "
        "complete Lean build closure, executable reproduction scripts, "
        "STATE snapshot + release-status markers, version/release coherence, "
        "landscape ledger, and strict-trust Lean sources"
    )


if __name__ == "__main__":
    main()
