import ast
from pathlib import Path


def _is_text_file_call(node: ast.AST) -> bool:
    if not isinstance(node, ast.Call):
        return False
    if isinstance(node.func, ast.Name) and node.func.id == "open":
        for kw in node.keywords:
            if kw.arg == "mode" and isinstance(kw.value, ast.Constant) and isinstance(kw.value.value, str) and "b" in kw.value.value:
                return False
        if len(node.args) >= 2 and isinstance(node.args[1], ast.Constant) and isinstance(node.args[1].value, str) and "b" in node.args[1].value:
            return False
        return True
    if isinstance(node.func, ast.Attribute) and node.func.attr in ("read_text", "write_text"):
        return True
    return False


def test_scripts_pass_explicit_encoding() -> None:
    scripts_dir = Path(__file__).resolve().parent.parent / "scripts"
    offenders: list[str] = []
    for path in sorted(scripts_dir.rglob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if _is_text_file_call(node) and not any(kw.arg == "encoding" for kw in node.keywords):
                offenders.append(f"{path.relative_to(scripts_dir.parent)}:{node.lineno}: {ast.unparse(node)}")
    assert not offenders, "Found text I/O calls without encoding=:\n" + "\n".join(offenders)
