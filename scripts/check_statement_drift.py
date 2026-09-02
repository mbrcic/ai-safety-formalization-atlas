#!/usr/bin/env python3
"""Report what a change did to statements, as opposed to what it did to proofs.

A toolchain migration is faithful when proof bodies may change and statements may
not.  Nothing in the gate could see that distinction: ``check_public_api.py`` pins
declaration *names*, so a hypothesis can be added or a class swapped without a
diff, and ``check_statement_freeze.py`` covers the graded statements only, which
leaves every vendored and off-root declaration unguarded.  The v4.33.0 migration
touched 54 files and both checks stayed green throughout.

The rule this applies:

* ``theorem``, ``lemma`` and ``example`` carry a **proof**, and the kernel checks
  it.  A proof that is wrong does not compile, so its text is not evidence of
  anything and is ignored — only the signature is compared.
* everything else — ``def``, ``abbrev``, ``instance``, ``structure``,
  ``inductive``, ``class``, ``axiom``, ``opaque``, notation and macros — carries
  **meaning in its body**, so the whole declaration is compared, with ``by``
  blocks masked.  Masking is a heuristic and not sound in general: a tactic block
  can build **data**, so ``def f : Nat := by exact 0`` and ``by exact 1`` mask to
  the same text.  Any non-theorem declaration that differs *only* inside a masked
  block is therefore reported for adjudication rather than dropped.
* ``import``, ``open``, ``variable``, ``set_option`` and ``attribute`` change what
  the declarations around them mean, so they are compared whole as well.

Run against any git ref.  Advisory by default: on a feature branch new theorems
are the point.  ``--fail-on-drift`` is for a migration, where the answer is
supposed to be none.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCES = "AISafetyAtlas"

# A proof is checked by the kernel, so its text carries no information a reader
# of this report needs.  Everything else means what its body says.
PROOF_KINDS = frozenset({"theorem", "lemma", "example"})
DECL_KINDS = frozenset({
    "theorem", "lemma", "example", "def", "abbrev", "instance", "structure",
    "inductive", "class", "axiom", "opaque", "macro", "macro_rules", "notation",
    "syntax", "elab", "elab_rules", "declare_syntax_cat", "initialize",
})
MODIFIERS = frozenset({
    "private", "public", "protected", "noncomputable", "partial", "unsafe",
    "nonrec", "scoped", "local", "mutual", "unseal", "recommended_spelling",
})
# Commands that are not declarations but do change what the file means.
CONTEXT_KINDS = frozenset({
    "import", "open", "namespace", "section", "end", "variable", "universe",
    "set_option", "attribute", "export", "deriving", "instance",
})
STARTERS = DECL_KINDS | MODIFIERS | CONTEXT_KINDS


def strip_comments(text: str) -> str:
    """Drop block comments, docstrings and line comments.

    Prose is not a statement.  Nesting is tracked because Lean's block comments
    nest and a `/- ... -/` inside a docstring would otherwise close it early.
    """
    out: list[str] = []
    index, depth, size = 0, 0, len(text)
    while index < size:
        if text.startswith("/-", index):
            depth += 1
            index += 2
            continue
        if text.startswith("-/", index) and depth:
            depth -= 1
            index += 2
            continue
        if depth:
            index += 1
            continue
        if text.startswith("--", index):
            newline = text.find("\n", index)
            index = size if newline < 0 else newline
            continue
        out.append(text[index])
        index += 1
    return "".join(out)


def starts_command(line: str) -> bool:
    """Whether a column-zero line opens a new top-level command.

    Not every column-zero line does: `| 0 => …` continues a pattern match, and
    `deriving …` continues an inductive.  Splitting on indentation alone merged
    those into their neighbours and made the report unreadable.
    """
    if not line or line[0].isspace():
        return False
    if line.startswith("@[") or line.startswith("#"):
        return True
    token = line.split(maxsplit=1)[0] if line.split() else ""
    return token.rstrip(":") in STARTERS


def signature(block: str) -> str:
    """The declaration up to the `:=` or `by` that opens its body."""
    depth = 0
    index = 0
    while index < len(block):
        char = block[index]
        if char in "([{⟨":
            depth += 1
        elif char in ")]}⟩":
            depth -= 1
        elif depth == 0:
            if block.startswith(":=", index):
                return block[:index]
            if (
                block.startswith("by", index)
                and (index == 0 or not (block[index - 1].isalnum() or block[index - 1] == "_"))
                and not (index + 2 < len(block) and (block[index + 2].isalnum() or block[index + 2] == "_"))
            ):
                return block[:index]
        index += 1
    return block


def strip_attributes(block: str) -> str:
    """Drop leading `@[…]` groups, counting brackets so nesting survives.

    Tokenizing first and looking for a `]` merged `@[simp] public theorem foo`
    into the kind `@`, which sent a theorem down the definition path and made its
    proof look like a statement change.
    """
    text = block.lstrip()
    while text.startswith("@["):
        depth, index = 0, 1
        while index < len(text):
            if text[index] == "[":
                depth += 1
            elif text[index] == "]":
                depth -= 1
                if depth == 0:
                    break
            index += 1
        text = text[index + 1 :].lstrip()
    return text


def kind_and_name(block: str) -> tuple[str, str]:
    text = strip_attributes(block)
    tokens = text.split()
    index = 0
    while index < len(tokens) and tokens[index] in MODIFIERS:
        index += 1
        text = " ".join(tokens[index:])
        text = strip_attributes(text)
        tokens = text.split()
        index = 0
    if not tokens:
        return ("", "")
    kind = tokens[0].rstrip(":")
    name = tokens[1].rstrip(":") if len(tokens) > 1 else ""
    if name.startswith(("(", "{", "[", ":", "⦃")):
        name = ""
    return (kind, name)


def mask_proofs(block: str) -> str:
    """Replace every `by …` span with a placeholder.

    A `by` block is a proof wherever it stands — as a declaration's body, as a
    structure field, or as a `Finset` membership argument buried in a term — and
    the kernel checks it, so its text is not a statement.  The span runs to the
    end of the bracket group that encloses the `by`, which is exactly how Lean
    scopes it.
    """
    out: list[str] = []
    index, depth = 0, 0
    size = len(block)
    while index < size:
        char = block[index]
        if char in "([{⟨":
            depth += 1
            out.append(char)
            index += 1
            continue
        if char in ")]}⟩":
            depth -= 1
            out.append(char)
            index += 1
            continue
        starts_by = (
            block.startswith("by", index)
            and (index == 0 or not (block[index - 1].isalnum() or block[index - 1] == "_"))
            and not (
                index + 2 < size and (block[index + 2].isalnum() or block[index + 2] == "_")
            )
        )
        if not starts_by:
            out.append(char)
            index += 1
            continue
        out.append("\u2039proof\u203a")
        opened = depth
        index += 2
        while index < size:
            if block[index] in "([{⟨":
                depth += 1
            elif block[index] in ")]}⟩":
                if depth == opened:
                    break
                depth -= 1
            index += 1
    return "".join(out)


def _blocks(text: str):
    """Every top-level command, with the namespace it sits in and its ordinal.

    Keying by the leaf name alone let `A.f` and `B.f` share a slot, so a change
    to one was masked by the other; four anonymous `instance :` declarations in
    one file collided the same way.  The namespace stack plus a per-key ordinal
    makes the key unique without needing to elaborate anything.
    """
    lines = strip_comments(text).split("\n")
    starts = [i for i, line in enumerate(lines) if starts_command(line)]
    # `section` shares the `end` keyword with `namespace` but contributes nothing
    # to a name, so both have to be on one stack.  Tracking only namespaces let a
    # bare `end` closing an unnamed section pop the enclosing *namespace*, and
    # every declaration after that point was keyed unqualified -- `Foo.b` became
    # `b`, which is a rename, which is a removal plus an addition.  No file in the
    # tree has that shape today; `check_drift_coverage.py` is what says so, by
    # comparing these keys against the names the environment reports.
    scopes: list[tuple[bool, str]] = []
    counter: Counter[tuple[str, str]] = Counter()
    for position, start in enumerate(starts):
        stop = starts[position + 1] if position + 1 < len(starts) else len(lines)
        block = " ".join(" ".join(lines[start:stop]).split())
        if not block:
            continue
        head = block.split()
        if head[0] == "namespace" and len(head) > 1:
            scopes.append((True, head[1]))
            continue
        if head[0] == "end":
            target = head[1] if len(head) > 1 else ""
            if target:
                for index in range(len(scopes) - 1, -1, -1):
                    if scopes[index][1] == target:
                        del scopes[index:]
                        break
            elif scopes:
                scopes.pop()
            continue
        if head[0] == "section":
            # Pushed, then still reported: a `section` line carries `variable`
            # scoping that a reader of the drift report needs to see.
            scopes.append((False, head[1] if len(head) > 1 else ""))
        namespace = [name for is_namespace, name in scopes if is_namespace]
        kind, name = kind_and_name(block)
        qualified = ".".join(namespace + [name]) if name else ".".join(namespace + ["<anonymous>"])
        counter[(kind, qualified)] += 1
        yield kind, qualified, counter[(kind, qualified)], block


def units(text: str) -> Counter[tuple[str, str, str]]:
    """Every comparable unit in one file, as (kind, qualified name, text)."""
    found: Counter[tuple[str, str, str]] = Counter()
    for kind, qualified, ordinal, block in _blocks(text):
        comparable = signature(block) if kind in PROOF_KINDS else mask_proofs(block)
        # Parenthesising a proof term changes nothing, and the migration added
        # brackets around several to make elaboration order explicit.
        comparable = comparable.replace("(\u2039proof\u203a)", "\u2039proof\u203a")
        found[(kind, qualified, " ".join(comparable.split()))] += 1
    return found


def proof_units(text: str) -> Counter[tuple[str, str, str]]:
    """The same units with proofs kept, so proof churn can be counted."""
    found: Counter[tuple[str, str, str]] = Counter()
    for kind, qualified, ordinal, block in _blocks(text):
        found[(kind, qualified, block)] += 1
    return found


def adjudications(before: str, after: str) -> list[tuple[str, str]]:
    """Non-theorem declarations that differ only inside a masked `by` block.

    Masking assumes a `by` block is a proof, and proofs are kernel-checked and
    proof-irrelevant.  That assumption is not sound in general: a tactic block
    can build **data**, and `def f : Nat := by exact 0` and `by exact 1` mask to
    the same text while denoting different numbers.  Such a pair is therefore
    never dropped silently — it is reported here for a human to adjudicate,
    which is the honest position for a textual check.
    """
    def index(text: str) -> tuple[dict, dict]:
        raw: dict[tuple[str, str, int], str] = {}
        masked: dict[tuple[str, str, int], str] = {}
        for kind, qualified, ordinal, block in _blocks(text):
            if not kind or kind in PROOF_KINDS:
                continue
            key = (kind, qualified, ordinal)
            raw[key] = block
            body = mask_proofs(block).replace("(\u2039proof\u203a)", "\u2039proof\u203a")
            masked[key] = " ".join(body.split())
        return raw, masked

    raw_before, masked_before = index(before)
    raw_after, masked_after = index(after)
    out = []
    for key in sorted(raw_before.keys() & raw_after.keys()):
        if masked_before[key] == masked_after[key] and raw_before[key] != raw_after[key]:
            out.append((f"{key[0]} {key[1]}".strip(), raw_after[key]))
    return out


def tree_at(ref: str) -> dict[str, str]:
    listing = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", ref, SOURCES],
        cwd=ROOT, capture_output=True, text=True, check=True,
    ).stdout.split()
    sources = [path for path in listing if path.endswith(".lean")]
    return {
        path: subprocess.run(
            ["git", "show", f"{ref}:{path}"],
            cwd=ROOT, capture_output=True, text=True, check=True,
        ).stdout
        for path in sources
    }


def working_tree() -> dict[str, str]:
    return {
        str(path.relative_to(ROOT)): path.read_text(encoding="utf-8")
        for path in sorted((ROOT / SOURCES).rglob("*.lean"))
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    # `origin/main` moves: after this branch merges it is no longer the
    # pre-migration tree. The v4.33.0 migration was measured against
    # 4edc04182b931a3ac0941d3b98120a6f1ca4fe85, which is what to pass to
    # reproduce that number.
    parser.add_argument("--ref", default="origin/main", help="git ref to compare against")
    parser.add_argument(
        "--fail-on-drift", action="store_true",
        help="exit non-zero when any statement changed (use for a toolchain migration)",
    )
    arguments = parser.parse_args()

    before = tree_at(arguments.ref)
    after = working_tree()

    drift: list[str] = []
    for path in sorted(set(before) - set(after)):
        drift.append(f"  removed file  {path}")
    for path in sorted(set(after) - set(before)):
        drift.append(f"  added file    {path}")

    compared = 0
    proofs_changed = 0
    adjudicate: list[str] = []
    for path in sorted(set(before) & set(after)):
        if before[path] == after[path]:
            compared += 1
            continue
        old, new = units(before[path]), units(after[path])
        compared += 1
        proofs_changed += sum(
            (proof_units(before[path]) - proof_units(after[path])).values()
        )
        for name, _ in adjudications(before[path], after[path]):
            adjudicate.append(f"  ? {path}  [{name}]")
        for unit in sorted(old - new):
            drift.append(f"  - {path}  [{unit[0]} {unit[1]}]\n      {unit[2][:240]}")
        for unit in sorted(new - old):
            drift.append(f"  + {path}  [{unit[0]} {unit[1]}]\n      {unit[2][:240]}")

    if adjudicate:
        print(
            f"adjudicate: {len(adjudicate)} non-theorem declaration(s) differ only inside a "
            f"masked `by` block. A tactic block usually proves something, and proofs are "
            f"kernel-checked, but one can also build data — read these before trusting the "
            f"line below."
        )
        for line in adjudicate:
            print(line)

    if drift:
        print(
            f"statement drift against {arguments.ref}: {len(drift)} difference(s); "
            f"{proofs_changed} proof body/bodies also rewritten (kernel-checked)"
        )
        for line in drift:
            print(line)
        if arguments.fail_on_drift:
            sys.exit(1)
        return
    if adjudicate:
        # An adjudication is unresolved by construction: the tool cannot tell a
        # proof from data, so it must not report "ok" over one, and a migration
        # asking for --fail-on-drift must stop here and get a human verdict.
        if arguments.fail_on_drift:
            sys.exit(1)
        return
    print(
        f"statement drift ok: {compared} Lean sources, no statement, definition, "
        f"instance, notation or file-level option differs from {arguments.ref}; "
        f"{proofs_changed} proof body/bodies rewritten (kernel-checked)"
    )


if __name__ == "__main__":
    try:
        main()
    except BrokenPipeError:
        # A caller that reads only the summary lines (`| head`) closes the pipe
        # while the per-declaration list is still being written. That is not an
        # error, but Python reports it again at interpreter shutdown unless
        # stdout is detached first.
        os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())
        sys.exit(0)
