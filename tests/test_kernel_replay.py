"""The kernel replay must still catch what it exists to catch.

`scripts/kernel_replay.lean` replaced `leanchecker` in `kernel_replay.sh` on
2026-10-12 because `leanchecker M` replays every module under the prefix M, which
made the nightly run replay each parent's subtree twice. Faster is only worth
having if the check is still effective, so these tests pin the behaviour:

* a module holding a theorem of `False` that was added with the kernel switched
  off (`debug.skipKernelTC`) must FAIL. `#print axioms` reports that theorem as
  depending on no axioms at all, which is why this check exists;
* an honest module must pass, and a pure aggregator must be skipped without
  being replayed;
* the replay function must still be the toolchain's own, byte for byte.

Fixtures are compiled into a temporary directory and put on LEAN_PATH, so
nothing is added to the atlas. Each case shells out to `lake env lean`, so they
are skipped where `lake` is absent.
"""

from __future__ import annotations

from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parent.parent
REPLAY = ROOT / "scripts/kernel_replay.lean"

pytestmark = [
    pytest.mark.lean,
    pytest.mark.skipif(shutil.which("lake") is None, reason="lake is not on PATH"),
]

FIXTURES = {
    "Honest": "theorem Honest.ok : True := True.intro\n",
    "Agg": "import Honest\n",
    "Hacked": (
        "import Lean\n"
        "open Lean Elab Command\n"
        "set_option debug.skipKernelTC true in\n"
        "run_cmd liftCoreM (addDecl (.thmDecl\n"
        "  { name := `Hacked.bad, levelParams := [], type := mkConst ``False,\n"
        "    value := mkConst ``True.intro }))\n"
        "theorem Hacked.uses : False := Hacked.bad\n"
    ),
}


def _lean(tmp: Path, *args: str) -> subprocess.CompletedProcess[str]:
    """Run `lean` from the repository root, with `tmp` ahead on LEAN_PATH.

    From the root so elan resolves the pinned toolchain: run anywhere else, it
    picks the default toolchain and the oleans no longer match the atlas's.
    """
    return subprocess.run(
        ["lake", "env", "bash", "-c", 'LEAN_PATH="$0:$LEAN_PATH" exec lean "$@"',
         str(tmp), *args],
        cwd=ROOT, capture_output=True, text=True, check=False,
    )


@pytest.fixture(scope="module")
def fixtures(tmp_path_factory: pytest.TempPathFactory) -> Path:
    tmp = tmp_path_factory.mktemp("kernel-replay")
    for name, source in FIXTURES.items():  # Honest before Agg, which imports it
        (tmp / f"{name}.lean").write_text(source, encoding="utf-8")
        built = _lean(tmp, f"--root={tmp}", "-o", str(tmp / f"{name}.olean"),
                      str(tmp / f"{name}.lean"))
        assert built.returncode == 0, built.stdout + built.stderr
    return tmp


def test_kernel_bypassed_theorem_is_rejected(fixtures: Path) -> None:
    run = _lean(fixtures, "--run", str(REPLAY), "Hacked")
    assert run.returncode != 0, run.stdout
    assert "while replaying declaration 'Hacked.bad'" in run.stdout + run.stderr


def test_honest_module_is_replayed(fixtures: Path) -> None:
    run = _lean(fixtures, "--run", str(REPLAY), "Honest")
    assert run.returncode == 0, run.stdout + run.stderr
    assert run.stdout.strip() == "ok Honest 1"


def test_aggregator_is_skipped(fixtures: Path) -> None:
    run = _lean(fixtures, "--run", str(REPLAY), "Agg")
    assert run.returncode == 0, run.stdout + run.stderr
    assert run.stdout.strip() == "skip Agg"


def test_replay_is_the_toolchains_own() -> None:
    prefix = subprocess.run(
        ["lake", "env", "lean", "--print-prefix"],
        cwd=ROOT, capture_output=True, text=True, check=True,
    ).stdout.strip()
    upstream = (Path(prefix) / "src/lean/LeanChecker.lean").read_text(encoding="utf-8")
    theirs = re.search(r"^unsafe def replayFromImports .*?(?=\n\n)", upstream,
                       re.S | re.M)
    ours = re.search(r"^-- BEGIN verbatim replayFromImports\n(.*?)\n"
                     r"-- END verbatim replayFromImports$",
                     REPLAY.read_text(encoding="utf-8"), re.S | re.M)
    assert theirs and ours
    assert ours.group(1) == theirs.group(0)
