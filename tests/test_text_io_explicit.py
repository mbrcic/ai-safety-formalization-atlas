"""Text I/O in ``scripts/`` and ``tests/`` names its encoding and its newline.

Python fills in both from the platform when a call leaves them out.  On the
Linux CI runners the defaults are UTF-8 and ``\\n``, so an omission is invisible
there.  On Windows the default encoding is a legacy code page and the default
newline is ``\\r\\n``, and the same omission did two things (issues #84, #85):

* a validator reading a ledger or a Lean source died with ``UnicodeDecodeError``
  on the first non-ASCII character it met, unless ``PYTHONUTF8=1`` was set;
* a gate run rewrote ``intake.yaml`` with CRLF line endings, because a test
  restored the file through ``write_text`` and left the working tree dirty.

Three rules follow, and this test holds every call site to them:

1. a text-mode ``open``, ``Path.open``, ``read_text``, ``write_text`` or
   temporary file passes ``encoding=``;
2. one that writes also passes ``newline=``;
3. a subprocess call that asks for text (``text=True``) passes ``encoding=``,
   since the child's output is decoded by the same platform default.

The standard streams are the one thing a call site cannot fix; ``agent_gate.sh``
pins them with ``PYTHONIOENCODING``.

The check reads the syntax tree and not the text, so a call spread over several
lines is seen whole, and a mention in a comment or a docstring is not a call.
What it cannot see is a call reached through an alias (``f = open``) or a mode
computed at run time; the second is reported so that it is looked at.
"""

from __future__ import annotations

import ast
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parent.parent
SCANNED = ("scripts", "tests")

SUBPROCESS_CALLS = {"run", "Popen", "check_output", "check_call", "call"}
TEMPORARY_FILES = {"NamedTemporaryFile", "TemporaryFile", "SpooledTemporaryFile"}


def _keyword(call: ast.Call, name: str) -> ast.keyword | None:
    return next((k for k in call.keywords if k.arg == name), None)


def _string(node: ast.expr | None) -> str | None:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    return None


def _open_mode(call: ast.Call, position: int) -> str | None:
    """The mode of an ``open`` call, or None when it is not a literal."""
    keyword = _keyword(call, "mode")
    if keyword is not None:
        return _string(keyword.value)
    if len(call.args) > position:
        return _string(call.args[position])
    return "r"


def problems_in(source: str) -> list[tuple[int, str]]:
    """``(line, what is missing)`` for every call in ``source`` that breaks a rule."""
    found: list[tuple[int, str]] = []
    for node in ast.walk(ast.parse(source)):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        if isinstance(func, ast.Name):
            name, method = func.id, False
        elif isinstance(func, ast.Attribute):
            name, method = func.attr, True
        else:
            continue

        has_encoding = _keyword(node, "encoding") is not None
        has_newline = _keyword(node, "newline") is not None
        reads_text = writes_text = False

        if name == "open":
            if method:
                # `Path.open(mode)`. Other things are called `.open` too --
                # `os.open(path, flags)`, an opener's `.open(request)` -- and
                # what tells them apart is that their first argument is not a
                # mode string.
                if node.args and _string(node.args[0]) is None:
                    continue
                mode = _open_mode(node, 0)
            else:
                mode = _open_mode(node, 1)
            if mode is None:
                found.append((node.lineno, "open() with a mode that is not a literal"))
                continue
            if "b" in mode:
                continue
            reads_text = True
            writes_text = any(flag in mode for flag in "wax+")
        elif method and name == "read_text":
            reads_text = True
            has_encoding = has_encoding or len(node.args) >= 1
        elif method and name == "write_text":
            reads_text = writes_text = True
            has_encoding = has_encoding or len(node.args) >= 2
        elif name in TEMPORARY_FILES:
            keyword = _keyword(node, "mode")
            if keyword is not None:
                mode = _string(keyword.value)
            elif node.args:
                mode = _string(node.args[0])
            else:
                mode = "w+b"
            if mode is None or "b" in mode:
                continue
            reads_text = writes_text = True
        elif name in SUBPROCESS_CALLS:
            if _keyword(node, "text") is None and _keyword(node, "universal_newlines") is None:
                continue
            if not has_encoding:
                found.append((node.lineno, f"{name}(text=True) without encoding="))
            continue

        if reads_text and not has_encoding:
            found.append((node.lineno, f"{name}() without encoding="))
        if writes_text and not has_newline:
            found.append((node.lineno, f"{name}() without newline="))
    return found


def _python_files() -> list[Path]:
    return sorted(p for d in SCANNED for p in (ROOT / d).rglob("*.py"))


def test_every_text_io_call_is_explicit() -> None:
    offenders = [
        f"{path.relative_to(ROOT).as_posix()}:{line}: {what}"
        for path in _python_files()
        for line, what in problems_in(path.read_text(encoding="utf-8"))
    ]
    assert not offenders, (
        "text I/O that takes its encoding or newline from the platform "
        '(pass encoding="utf-8", and newline="\\n" when writing):\n  '
        + "\n  ".join(offenders)
    )


# The detector is the whole test, so it is tested: each line below is a call the
# rules reject, and a detector that passed any of them would pass the tree.
@pytest.mark.parametrize(
    "call",
    [
        "open(p)",
        'open(p, "w", encoding="utf-8")',
        'open(p, "a", newline="\\n")',
        "open(p, mode)",
        "p.open()",
        'p.open("w", encoding="utf-8")',
        "p.read_text()",
        "p.write_text(s)",
        'p.write_text(s, encoding="utf-8")',
        'p.write_text(s, newline="\\n")',
        'tempfile.NamedTemporaryFile("w", encoding="utf-8")',
        "subprocess.run(cmd, capture_output=True, text=True)",
        "subprocess.check_output(cmd, universal_newlines=True)",
    ],
)
def test_the_detector_rejects(call: str) -> None:
    assert problems_in(call), call


@pytest.mark.parametrize(
    "call",
    [
        'open(p, encoding="utf-8")',
        'open(p, "rb")',
        'open(p, "w", encoding="utf-8", newline="\\n")',
        'open(p, mode="wb")',
        'p.open("rb")',
        'p.open(encoding="utf-8")',
        'p.read_text(encoding="utf-8")',
        'p.read_text("utf-8")',
        'p.write_text(s, encoding="utf-8", newline="\\n")',
        "p.read_bytes()",
        "os.open(os.devnull, os.O_WRONLY)",
        "opener.open(request, timeout=5)",
        "tempfile.NamedTemporaryFile()",
        'tempfile.NamedTemporaryFile("w", encoding="utf-8", newline="\\n")',
        "subprocess.run(cmd, capture_output=True)",
        'subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")',
    ],
)
def test_the_detector_accepts(call: str) -> None:
    assert not problems_in(call), call
