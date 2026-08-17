"""Regression tests for the two coverage-audit gate scripts.

Both scripts were defeated repeatedly during review, so each check they carry is
pinned here. The three added on 2026-08-16 are at the bottom: the registry-row
check, the heading-form guard that keeps it alive, and the renderer's rejection
of an unrecognized flag — which had silently written a file named `--write` and
left the published artifact stale.
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = ROOT / "scripts"


def _load(name: str):
    # `scripts/` modules import each other by bare name
    if str(SCRIPTS) not in sys.path:
        sys.path.insert(0, str(SCRIPTS))
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / f"{name}.py")
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


audit = _load("check_coverage_audit")


# --- the audit's own state stays consistent ------------------------------------


def test_gate_scripts_pass_on_the_repository():
    for script in ("check_coverage_audit.py", "render_coverage_artifact.py"):
        args = [sys.executable, str(SCRIPTS / script)]
        if script == "render_coverage_artifact.py":
            args.append("--check")
        result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
        assert result.returncode == 0, f"{script}: {result.stderr}"


# --- declaration-name resolution ------------------------------------------------


def test_atlas_shaped_name_that_resolves_is_accepted():
    known = {"fano_of_log_le", "AISafetyAtlas.InformationTheory.fano_of_log_le"}
    assert audit.check_name("fano_of_log_le", known, set()) == []


def test_all_lowercase_fake_is_rejected():
    # the shape that defeated an earlier revision: a plausible lowercase name
    # with an underscore, resolving to nothing
    assert audit.check_name("fano_of_lag_le", {"fano_of_log_le"}, set()) != []


def test_real_tail_under_a_fictional_namespace_is_rejected():
    known = {"fano", "AISafetyAtlas.InformationTheory.fano"}
    assert audit.check_name("AISafetyAtlas.Nonsense.fano", known, set()) != []


def test_lowercase_mathlib_names_are_allowed():
    for name in sorted(audit.EXTERNAL_LOWERCASE):
        assert audit.check_name(name, set(), set()) == []


def test_a_script_is_allowed_only_when_the_file_exists():
    assert audit.check_name("check_coverage_audit.py", set(), set()) == []
    assert audit.check_name("check_nothing_at_all.py", set(), set()) != []


def test_a_fake_script_with_no_underscore_is_still_rejected():
    # `nosuch.py` has no underscore and no internal capital, so the shape
    # heuristics below the script branch never fire on it
    assert audit.check_name("nosuch.py", set(), set()) != []


# --- every graded section must declare a target, not just those that do -------


def test_graded_section_without_a_target_heading_is_reported():
    declared = audit.audit_declared_headings(
        "## 1. Cover & Thomas, §2.8 → `AISafetyAtlas.InformationTheory.DataProcessing`\n"
        "## 2. Touchette & Lloyd 2004\n"
    )
    assert declared == {
        "Cover & Thomas, §2.8 → `AISafetyAtlas.InformationTheory.DataProcessing`"
    }


def test_declared_headings_match_the_section_parser_keys():
    text = (ROOT / "docs" / "provenance" / "source-coverage-audit.md").read_text()
    per_section, _, _, _ = audit.parse_sections(text)
    declared = audit.audit_declared_headings(text)
    graded = {name for name, counts in per_section.items() if any(counts.values())}
    assert graded <= declared, f"graded sections declaring no target: {graded - declared}"


# --- validate_registry's build_command targets --------------------------------


registry = _load("validate_registry")


def test_lean_module_shape_accepts_module_paths_and_rejects_prose():
    assert registry.LEAN_MODULE_SHAPE.match("AISafetyAtlas.Control.RequisiteVariety")
    assert registry.LEAN_MODULE_SHAPE.match("Mathlib.Totally.Fictional")
    assert registry.LEAN_MODULE_SHAPE.match("Aisafetyatlas.Control.NoSuchModule")
    assert not registry.LEAN_MODULE_SHAPE.match("scripts/reproduce_isabelle.sh")
    assert not registry.LEAN_MODULE_SHAPE.match("done")


@pytest.mark.parametrize("module", [
    "Mathlib.Totally.Fictional",
    "AISafetyAtlas.Control.NoSuchModule",
    "Aisafetyatlas.Control.RequisiteVariety",
])
def test_nonexistent_modules_do_not_resolve(module):
    assert not registry.lean_module_exists(module)


def test_real_modules_resolve_in_tree_and_in_packages():
    assert registry.lean_module_exists("AISafetyAtlas.Control.RequisiteVariety")
    assert registry.lean_module_exists("PFR.ForMathlib.Entropy.Basic")


# --- the registry-row check, added 2026-08-16 -----------------------------------


def test_every_graded_module_is_hosted_by_a_registry_row():
    text = (ROOT / "docs" / "provenance" / "source-coverage-audit.md").read_text()
    targets = audit.audit_target_modules(text)
    assert targets, "no section heading names a target module"
    hosted = audit.registry_modules()
    unhosted = [(h, m) for h, m in targets if m not in hosted]
    assert not unhosted, f"modules graded but not registered: {unhosted}"


def test_heading_parser_reads_the_arrow_form():
    text = "\n".join([
        "## 1. Cover & Thomas, §2.8 → `AISafetyAtlas.InformationTheory.DataProcessing`",
        "some prose",
        "## Totals",
    ])
    assert audit.audit_target_modules(text) == [
        ("Cover & Thomas, §2.8", "AISafetyAtlas.InformationTheory.DataProcessing")
    ]


def test_heading_parser_returns_nothing_when_the_form_changes():
    # the guard in main() turns this into a failure rather than a silent pass
    text = "## 1. Cover & Thomas, §2.8 (AISafetyAtlas.InformationTheory.DataProcessing)"
    assert audit.audit_target_modules(text) == []


# --- the artifact renderer's argument handling, added 2026-08-16 ----------------


@pytest.mark.parametrize("flag", ["--write", "--force", "-w"])
def test_renderer_rejects_an_unknown_flag(flag, tmp_path):
    result = subprocess.run(
        [sys.executable, str(SCRIPTS / "render_coverage_artifact.py"), flag],
        cwd=tmp_path, capture_output=True, text=True,
    )
    assert result.returncode == 2, result.stdout
    assert "unknown option" in result.stderr
    assert not (tmp_path / flag).exists(), "the flag was written as an output file"


def test_renderer_rejects_two_output_paths(tmp_path):
    result = subprocess.run(
        [sys.executable, str(SCRIPTS / "render_coverage_artifact.py"),
         str(tmp_path / "a.html"), str(tmp_path / "b.html")],
        cwd=tmp_path, capture_output=True, text=True,
    )
    assert result.returncode == 2, result.stdout


def test_renderer_check_detects_a_stale_artifact(tmp_path):
    out = tmp_path / "coverage-audit.html"
    out.write_text("<p>stale</p>")
    result = subprocess.run(
        [sys.executable, str(SCRIPTS / "render_coverage_artifact.py"), "--check", str(out)],
        cwd=ROOT, capture_output=True, text=True,
    )
    assert result.returncode != 0, "a stale artifact passed --check"
