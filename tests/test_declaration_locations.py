"""Every ledger declaration must resolve to the file and line it is defined at.

`docs/agent/by-id.json` exists so an agent can open a declaration without
searching the repository. A name that does not resolve silently reverts that
lookup to a repository-wide grep, and nothing else in the gate notices: the
registry validator checks that the *module* exists, not that the declaration
does, and the public page only links one declaration per row.

Two properties are pinned here.

* **Scope tracking.** `section … end` and `namespace … end` close with the same
  keyword. A scope stack that pushes only for `namespace` pops the enclosing
  namespace at a section's `end`, and every declaration after it resolves under
  a truncated prefix. Four ledger declarations were unreachable that way.
* **Completeness.** Every declaration the ledger publishes resolves. This is the
  property that surfaced the bug above, and it is the one that keeps a future
  scope construct from reintroducing it.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from generate_registry_views import declaration_locations  # noqa: E402


def ledger_declarations() -> list[str]:
    registry = json.loads((ROOT / "registry.yaml").read_text(encoding="utf-8"))
    names: list[str] = []
    for result in registry["results"]:
        artifact = result.get("lean_artifact")
        if not artifact:
            continue
        for declaration in artifact.get("declarations") or []:
            names.append(declaration["atlas_declaration"])
    return names


def test_every_ledger_declaration_resolves() -> None:
    locations = declaration_locations()
    unresolved = [name for name in ledger_declarations() if name not in locations]
    assert not unresolved, (
        "these ledger declarations resolve to no definition site, so the agent "
        f"index cannot point at them: {unresolved}"
    )


def test_locations_point_at_the_declaration() -> None:
    """The recorded line must be the one the declaration is written on."""
    locations = declaration_locations()
    for name in ledger_declarations():
        relative, number = locations[name]
        line = (ROOT / relative).read_text(encoding="utf-8").splitlines()[number - 1]
        final = name.rsplit(".", 1)[-1]
        assert final in line, (
            f"{name} is recorded at {relative}:{number}, which reads {line!r}"
        )


def test_section_end_does_not_close_the_namespace() -> None:
    """The regression itself, on a declaration that follows a closed section."""
    locations = declaration_locations()
    assert "AISafetyAtlas.Preference.ReasonableLanguage.proposition_seven" in locations
    assert "AISafetyAtlas.Preference.ReasonableLanguage.proposition_eight" in locations
