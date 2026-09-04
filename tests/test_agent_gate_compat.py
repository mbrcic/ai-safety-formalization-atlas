"""Compatibility smoke test for the quiet agent-gate path.

The quiet wrapper invokes the gate recursively.  Bash 3.2, still shipped by
macOS, treats an empty array expansion under ``set -u`` as an unbound variable,
so this must exercise the actual recursive call rather than merely parse it.
"""

from __future__ import annotations

import os
import shutil
import stat
import subprocess
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parent.parent
BASH = Path("/bin/bash")


def _stub(path: Path) -> None:
    path.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)


@pytest.mark.skipif(not BASH.is_file(), reason="agent_gate.sh requires Bash")
def test_quiet_mode_runs_under_nounset(tmp_path: Path) -> None:
    """A minimal fake checkout reaches the wrapper without running real gates."""
    root = tmp_path / "atlas"
    scripts = root / "scripts"
    scripts.mkdir(parents=True)
    gate = scripts / "agent_gate.sh"
    shutil.copy2(ROOT / "scripts" / "agent_gate.sh", gate)

    stub_bin = tmp_path / "bin"
    stub_bin.mkdir()
    for name in ("python3", "git", "ty", "pytest"):
        _stub(stub_bin / name)

    environment = dict(os.environ)
    environment["PATH"] = f"{stub_bin}{os.pathsep}{environment['PATH']}"
    result = subprocess.run(
        [str(BASH), str(gate), "--quiet"],
        cwd=root,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode == 0, result.stdout + result.stderr
    assert "agent_gate: ok (quiet; full checks passed)" in result.stdout
