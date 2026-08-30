import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "check_statement_freeze", ROOT / "scripts" / "check_statement_freeze.py")
assert SPEC is not None and SPEC.loader is not None
FREEZE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(FREEZE)


def test_every_graded_conjecture_declaration_is_frozen() -> None:
    rows = json.loads((ROOT / "conjectures.yaml").read_text())["conjectures"]
    expected = {
        row["lean"]
        for row in rows
        if row.get("lean") and row.get("source_fidelity")
    }

    assert expected <= FREEZE.current().keys()
