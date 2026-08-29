#!/usr/bin/env python3
"""Tell a contributor what *this* change obliges them to do, and nothing else.

The project's rules run to roughly a thousand lines across `AGENTS.md`,
`CONTRIBUTING.md`, `docs/guide/methodology.md` and `docs/guide/conjectures.md`.
Most of them do not apply to any one change. A newcomer — or an agent working
on their behalf — currently reads all of it to find the twenty lines that do,
and the cost of that is paid on every first contribution.

This script reads the diff, decides which kinds of contribution it contains,
and prints the obligations and commands for those kinds only.

**It restates no rule.** Every obligation below names the file and section that
governs it, and the wording there is authoritative. That is deliberate: a
second copy of the rules is a second source of truth, it drifts, and nothing
would catch the drift. What is duplicated here is the *routing*, which is
cheap to keep honest — `scripts/check_docs_paths.py` fails if a path named
here stops existing.

It is advisory and always exits 0. The gate decides what is broken; this
decides what to think about before running it.

Usage:
    python3 scripts/preflight.py               # against origin/main
    python3 scripts/preflight.py --base HEAD~3
    python3 scripts/preflight.py --staged      # only what is staged
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


# Each kind: the paths that mean "this change is of that kind", the obligations
# a reviewer will check, and where the binding wording lives. Obligations are
# imperative and short; the pointer is what a contributor should actually read.
# Each kind names the sections that govern it and the commands to run. It does
# NOT paraphrase them: the text printed is sliced out of the named file at
# runtime, so the wording a contributor reads is the wording that binds, and a
# renamed heading fails loudly instead of silently pointing at nothing.
KINDS: dict[str, dict] = {
    "lean-library": {
        "title": "Lean library change (a module under AISafetyAtlas/, not Examples/)",
        "sections": [
            ("AGENTS.md", "Every library module needs a worked model"),
            ("AGENTS.md", "Lean surface rule"),
            ("AGENTS.md", "Statement freeze"),
            ("AGENTS.md", "Parsimony (formalizations)"),
        ],
        "commands": [
            "python3 scripts/check_statement_freeze.py",
            "lake build",
            "xargs lake build < scripts/lean_build_targets.txt",
            "python3 scripts/check_print_axioms.py",
        ],
    },
    "lean-examples": {
        "title": "Example or witness (AISafetyAtlas/Examples/)",
        "sections": [
            ("AGENTS.md", "Examples layout rule"),
            ("AGENTS.md", "Every library module needs a worked model"),
        ],
        "commands": [
            "python3 scripts/check_examples_layout.py",
            "xargs lake build < scripts/lean_build_targets.txt",
        ],
    },
    "ledger": {
        "title": "Registry or conjecture ledger (registry.yaml, conjectures.yaml)",
        "sections": [
            ("CONTRIBUTING.md", "Evidence and registry changes"),
            ("AGENTS.md", "Coverage, landscape, and bridges"),
        ],
        "commands": [
            "python3 scripts/generate_registry_views.py",
            "python3 scripts/validate_registry.py",
            "python3 scripts/validate_conjectures.py",
        ],
    },
    "generated": {
        "title": "Generated file — edit the source, not the output",
        "sections": [("AGENTS.md", "Documentation layout")],
        "commands": [
            "python3 scripts/generate_registry_views.py",
            "python3 scripts/generate_dependency_graph.py --write",
            "python3 scripts/generate_non_claims.py --write",
        ],
    },
    "docs": {
        "title": "Documentation",
        "sections": [
            ("AGENTS.md", "Documentation layout"),
            ("AGENTS.md", "Audience and wording"),
        ],
        "commands": [
            "python3 scripts/check_docstring_identifiers.py",
            "python3 scripts/check_docs_paths.py",
        ],
    },
    "tooling": {
        "title": "Scripts, tests, or CI",
        "sections": [("AGENTS.md", "Validation")],
        "commands": ["python3 -m pytest -q tests/", "ty check"],
    },
}

HEADING_RE = re.compile(r"^(#{2,4})\s+(.*?)\s*$")


def section_text(filename: str, heading: str) -> str:
    """The named section, verbatim, from the file that owns it.

    Raises if the heading is gone. That is the point: routing that silently
    points at a renamed section is worse than no routing, because it still
    looks authoritative.
    """
    lines = (ROOT / filename).read_text(encoding="utf-8").split("\n")
    starts: list[tuple[int, str, str]] = []
    for number, line in enumerate(lines):
        match = HEADING_RE.match(line)
        if match:
            starts.append((number, match.group(1), match.group(2)))
    for index, (line_no, hashes, title) in enumerate(starts):
        if title != heading:
            continue
        end = len(lines)
        for later_no, later_hashes, _ in starts[index + 1:]:
            if len(later_hashes) <= len(hashes):
                end = later_no
                break
        return "\n".join(lines[line_no + 1:end]).strip("\n")
    raise SystemExit(
        f"preflight: {filename} has no section {heading!r}. Either the heading "
        f"was renamed — update the reference in this script — or it was deleted, "
        f"in which case the rule it carried needs a new home."
    )


def classify(path: str) -> list[str]:
    """Every kind a single changed path implies."""
    kinds = []
    if path.startswith("AISafetyAtlas/Examples/"):
        kinds.append("lean-examples")
    elif path.startswith("AISafetyAtlas/") and path.endswith(".lean"):
        kinds.append("lean-library")
    elif path in {"AISafetyAtlas.lean", "Main.lean"}:
        kinds.append("lean-library")
    if path in {"registry.yaml", "conjectures.yaml"}:
        kinds.append("ledger")
    if path.startswith("docs/status/") or path == "docs/guide/contributor-tasks.md":
        kinds.append("generated")
    elif path.startswith("docs/") or path.endswith(".md"):
        kinds.append("docs")
    if path.startswith(("scripts/", "tests/", ".github/")):
        kinds.append("tooling")
    return kinds


def changed_paths(base: str, staged: bool) -> list[str]:
    if staged:
        cmd = ["git", "diff", "--cached", "--name-only"]
    else:
        merge_base = subprocess.run(
            ["git", "merge-base", "HEAD", base], cwd=ROOT,
            capture_output=True, text=True,
        )
        ref = merge_base.stdout.strip() or base
        cmd = ["git", "diff", "--name-only", ref]
    result = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    return [p for p in result.stdout.split("\n") if p.strip()]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Print the obligations that apply to the current change.")
    parser.add_argument("--base", default="origin/main",
                        help="compare against this ref (default: origin/main)")
    parser.add_argument("--brief", action="store_true",
                        help="headings and commands only, no section text — the "
                             "cheap re-run once the sections have been read")
    parser.add_argument("--staged", action="store_true",
                        help="use the staged diff instead of a ref comparison")
    args = parser.parse_args()

    paths = changed_paths(args.base, args.staged)
    if not paths:
        print("preflight: no changes detected.")
        print()
        print("Starting from nothing? The cheapest first contribution is a")
        print("declaration with no downstream consumer — see the work_queue in")
        print("docs/status/consumers.json, and docs/guide/contributor-tasks.md")
        print("for bounded units. Read AGENTS.md and docs/agent/INDEX.md first;")
        print("everything else is conditional on what you touch.")
        return 0

    found: dict[str, list[str]] = {}
    for path in paths:
        for kind in classify(path):
            found.setdefault(kind, []).append(path)

    print(f"preflight: {len(paths)} changed path(s), "
          f"{len(found)} contribution kind(s).\n")
    print("Advisory. The text below is sliced verbatim out of the files that")
    print("govern it — nothing here is a paraphrase. Re-run with --brief once")
    print("you have read it; the gate is what actually decides.\n")

    commands: list[str] = []
    printed: set[tuple[str, str]] = set()
    for kind in KINDS:
        if kind not in found:
            continue
        spec = KINDS[kind]
        files = found[kind]
        print("=" * 72)
        print(spec["title"])
        shown = ", ".join(files[:3]) + (f" (+{len(files) - 3})" if len(files) > 3 else "")
        print(f"  triggered by: {shown}\n")
        for filename, heading in spec["sections"]:
            if args.brief:
                print(f"  read: {filename} § {heading}")
                continue
            if (filename, heading) in printed:
                print(f"  [{filename} § {heading} — printed above]\n")
                continue
            printed.add((filename, heading))
            print(f"  ── {filename} § {heading} " + "─" * max(0, 48 - len(heading)))
            body = section_text(filename, heading)
            for line in body.split("\n"):
                print(f"  {line}" if line else "")
            print()

        for command in spec["commands"]:
            if command not in commands:
                commands.append(command)

    print("=" * 72)
    print("Run, in this order:\n")
    for command in commands:
        print(f"  {command}")
    print("  ./scripts/agent_gate.sh          # everything mechanical")
    print()
    print("`agent_gate.sh --fast` is the retry loop once the gate has failed")
    print("once. The full gate is owed before the commit either way.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
