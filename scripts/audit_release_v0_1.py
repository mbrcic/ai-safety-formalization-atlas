#!/usr/bin/env python3
"""Audit only the immutable evidence recorded for the v0.1 release."""

from __future__ import annotations

from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        print(f"v0.1 release audit error: {message}", file=sys.stderr)
        raise SystemExit(1)


def git_output(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )


def approval_anchor_status(approved_ref: str) -> tuple[str, str | None]:
    """Classify local reachability without printing private ref names."""
    commit = git_output("cat-file", "-e", f"{approved_ref}^{{commit}}")
    if commit.returncode != 0:
        return "unavailable", None

    tree = git_output("rev-parse", f"{approved_ref}^{{tree}}")
    tree_ref = tree.stdout.strip() if tree.returncode == 0 else None

    remote_refs = git_output(
        "for-each-ref",
        f"--contains={approved_ref}",
        "--format=%(refname)",
        "refs/remotes",
    )
    if remote_refs.returncode == 0 and remote_refs.stdout.strip():
        return "fetched-remote", tree_ref

    tag_refs = git_output(
        "for-each-ref",
        f"--contains={approved_ref}",
        "--format=%(refname)",
        "refs/tags",
    )
    if tag_refs.returncode == 0 and tag_refs.stdout.strip():
        return "local-tag", tree_ref

    return "local-only", tree_ref


def main() -> None:
    release_path = ROOT / "docs/releases/v0.1.md"
    require(release_path.is_file(), "docs/releases/v0.1.md is missing")
    release_doc = release_path.read_text(encoding="utf-8")

    evidence = [
        "| Verified formalization records | 9 records | Passed |",
        "| Lean facade or bridge theorems | 7 compiled declarations | Passed |",
        "| Verified survey-row coverage | 3 of 44 results | Explicitly partial |",
        "| Reviewed AI-system bridge theorems | 0 | Explicitly deferred |",
    ]
    require(
        all(line in release_doc for line in evidence),
        "immutable v0.1 objective evidence has changed",
    )

    approval_match = re.search(
        r"^- Approval ref: `([0-9a-f]{40})`$", release_doc, re.MULTILINE
    )
    require(
        approval_match is not None,
        "release document must record a full immutable approval ref",
    )
    approved_ref = approval_match.group(1)
    require(
        "- Publication status: approved for publication" in release_doc,
        "release document must record publication approval",
    )
    require(
        f"| Maintainer approval | Approved for immutable ref `{approved_ref}` | Passed |"
        in release_doc,
        "release document approval evidence does not match its approval ref",
    )

    anchor_status, tree_ref = approval_anchor_status(approved_ref)
    tree_note = f", tree {tree_ref[:12]}" if tree_ref else ""
    explanations = {
        "fetched-remote": "reachable from fetched remote history",
        "local-tag": "reachable from a local tag; remote publication is unverified",
        "local-only": "available only in local history; not publicly reproducible",
        "unavailable": "not available in this checkout",
    }
    print(
        f"v0.1 release evidence ok: immutable approval {approved_ref[:12]}"
        f"{tree_note}; anchor {anchor_status} ({explanations[anchor_status]})"
    )


if __name__ == "__main__":
    main()
