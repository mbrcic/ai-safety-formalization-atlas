"""The validators claim a Python floor; this checks the claim both ways.

The floor was not chosen, it was measured: ``str.removesuffix``,
``str.removeprefix`` and ``functools.cache`` are all 3.9, and ten call sites
across six validators use them.  Nothing in ``scripts/`` or ``tests/`` needs
3.10 or later, so 3.9 is the real requirement rather than a convenient one.

Two failures are possible and both matter.  A script that reaches for a newer
feature silently raises the floor, and on Ubuntu 20.04 -- whose ``python3`` is
still 3.8 -- that surfaces as an ``AttributeError`` from inside whichever
validator happened to run first, which reads as a bug in that validator.  A
document or bootstrap script that names a different floor from the one the code
needs sends a contributor to the same place by a longer route.
"""

from __future__ import annotations

import ast
import os
import subprocess
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parent.parent
FLOOR = (3, 9)

# Syntax is left to the parser: ast.parse(..., feature_version=FLOOR) rejects
# match statements, except*, PEP 695 type aliases and generic parameter lists
# with the version that introduced each. Enumerating them by hand was the first
# version of this test and it accepted except* -- the parser knows the whole
# grammar and a list does not.
#
# What feature_version does not decide is the standard library, so the two
# tables below carry the parts of it that moved after the floor. It also does
# not reject `int | None` inside an annotation, which is correct: every module
# here uses `from __future__ import annotations`, so an annotation is never
# evaluated. A PEP 604 union in a *runtime* position -- isinstance, a cast, a
# default -- would run on 3.9 and is not caught here.
ATTRIBUTES_ABOVE_FLOOR = {
    "batched": (3, 12),  # itertools
    "pairwise": (3, 10),  # itertools
}
MODULES_ABOVE_FLOOR = {
    "tomllib": (3, 11),
}


def _sources() -> list[Path]:
    paths = [
        path
        for directory in ("scripts", "tests")
        for path in sorted((ROOT / directory).rglob("*.py"))
        if "__pycache__" not in path.parts
    ]
    assert paths, "no Python sources found; the layout moved"
    return paths


@pytest.mark.parametrize("path", _sources(), ids=lambda p: str(p.relative_to(ROOT)))
def test_source_stays_within_the_declared_floor(path: Path) -> None:
    """No script uses syntax or a library API newer than the floor."""
    source = path.read_text(encoding="utf-8")
    try:
        tree = ast.parse(source, filename=str(path), feature_version=FLOOR)
    except SyntaxError as error:  # pragma: no cover - the failure this guards
        pytest.fail(
            f"{path.relative_to(ROOT)} does not parse as Python "
            f"{FLOOR[0]}.{FLOOR[1]}: line {error.lineno}: {error.msg}"
        )

    offences: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Attribute) and node.attr in ATTRIBUTES_ABOVE_FLOOR:
            version = ATTRIBUTES_ABOVE_FLOOR[node.attr]
            offences.append(
                f"line {node.lineno}: .{node.attr} needs {version[0]}.{version[1]}"
            )
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            names = (
                [alias.name for alias in node.names]
                if isinstance(node, ast.Import)
                else [node.module or ""]
            )
            for name in names:
                version = MODULES_ABOVE_FLOOR.get(name.split(".")[0])
                if version is not None:
                    offences.append(
                        f"line {node.lineno}: {name} needs {version[0]}.{version[1]}"
                    )

    assert not offences, (
        f"{path.relative_to(ROOT)} exceeds the declared Python "
        f"{FLOOR[0]}.{FLOOR[1]} floor:\n  " + "\n  ".join(offences)
    )


@pytest.mark.parametrize(
    "relative_path",
    ["scripts/setup.sh", "scripts/agent_gate.sh"],
)
def test_bootstrap_guards_the_same_floor(relative_path: str) -> None:
    """Both entry points refuse an interpreter below the floor, in the same words."""
    text = (ROOT / relative_path).read_text(encoding="utf-8")
    guard = f"sys.version_info >= ({FLOOR[0]}, {FLOOR[1]})"
    assert guard in text, (
        f"{relative_path} does not check for Python {FLOOR[0]}.{FLOOR[1]}; "
        "a contributor below the floor meets an AttributeError instead of a sentence"
    )
    assert f"Python {FLOOR[0]}.{FLOOR[1]} or newer" in text, (
        f"{relative_path} checks the floor but does not name it in the error"
    )


def test_readme_names_the_floor() -> None:
    """The onboarding claim matches what the code needs."""
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    assert "pure-stdlib Python 3" not in readme, (
        "README claims a pure-stdlib requirement; check_conjecture_grade_prose "
        "imports PyYAML and six validators need 3.9"
    )
    assert f"Python {FLOOR[0]}.{FLOOR[1]} or\nnewer" in readme, (
        "README does not state the Python floor the validators enforce"
    )


def test_the_floor_test_would_notice_newer_syntax(tmp_path: Path) -> None:
    """The parser check is load-bearing: syntax above the floor must not pass.

    ``except*`` is the case that motivated it. The first version of this file
    enumerated constructs by hand, and a hand-written list has no reason to
    contain a construct nobody has used yet.
    """
    for source, introduced in (
        ("try:\n    pass\nexcept* ValueError:\n    pass\n", "3.11"),
        ("match x:\n    case 1:\n        pass\n", "3.10"),
        ("type Alias = int\n", "3.12"),
    ):
        with pytest.raises(SyntaxError):
            ast.parse(source, feature_version=FLOOR)
        assert ast.parse(source), f"the {introduced} sample is not valid on this interpreter"


def test_suite_collects_without_pyyaml(tmp_path: Path) -> None:
    """PyYAML absent must skip a module, not interrupt collection.

    agent_gate.sh skips the standalone conjecture-prose check when PyYAML is
    missing, but the checker is also imported by a pytest module. Without a
    skip there, the gate's own pytest step fails collection and takes the whole
    suite with it -- so the gate's notice would promise something untrue.
    """
    blocker = tmp_path / "sitecustomize.py"
    blocker.write_text("import sys\nsys.modules['yaml'] = None\n", encoding="utf-8")

    environment = dict(os.environ)
    existing = environment.get("PYTHONPATH")
    environment["PYTHONPATH"] = (
        str(tmp_path) if existing is None else f"{tmp_path}{os.pathsep}{existing}"
    )

    result = subprocess.run(
        [
            sys.executable, "-m", "pytest",
            str(ROOT / "tests" / "test_conjecture_grade_prose.py"),
            "-q", "--no-header", "-p", "no:cacheprovider",
        ],
        cwd=ROOT,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
    )

    # 0 is a clean run and 5 is "everything in this run was skipped"; the
    # regression is 2, which pytest returns for an interrupted collection and
    # which takes every other test module down with it.
    assert result.returncode in (0, 5), (
        "PyYAML absent interrupted collection:\n" + result.stdout + result.stderr
    )
    assert "skipped" in result.stdout, result.stdout
    assert "error" not in result.stdout.lower(), result.stdout
