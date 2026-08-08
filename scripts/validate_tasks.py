#!/usr/bin/env python3
"""Validate the contributor task ledger.

`tasks.yaml` is the one maintained record; `docs/guide/contributor-tasks.md` is
generated from it. This checks schema, cross-references, and internal
consistency — never whether a task is worth doing, which is a human judgement
and stays in the prose body.

The specific drift this closes: a task's done/open state used to live in a
Markdown badge only, so the board and the issues could disagree with each other
and with reality. `status` and the rendered badge must now agree, and every
result id a task cites must exist.
"""

from __future__ import annotations

import json
from pathlib import Path
import re
import sys
from typing import Any, NoReturn, cast


ROOT = Path(__file__).resolve().parents[1]
TASKS = ROOT / "tasks.yaml"
REGISTRY = ROOT / "registry.yaml"
TASK_ID = re.compile(r"CT-\d+")
RESULT_REF = re.compile(r"\bBY-\d{3}\b")
CLAIM_REF = re.compile(r"\bCLM-[A-Z0-9-]+\b")
LANDSCAPE_REF = re.compile(r"\bLAND-[A-Z0-9-]+\b")
SIZES = {"S", "M", "L"}
STATUSES = {"OPEN", "DONE"}
REQUIRED = {"id", "title", "size", "rung", "status", "heading_level", "body"}


def fail(message: str) -> NoReturn:
    print(f"tasks error: {message}", file=sys.stderr)
    raise SystemExit(1)


def require_mapping(value: object, message: str) -> dict[str, Any]:
    """Return `value` as a JSON object, or fail with an actionable reason.

    `isinstance(value, dict)` narrows only to `dict[Unknown, Unknown]`, whose
    key type is `Never`, so every subsequent subscript reads as an error. One
    spelling for "this must be an object" keeps the narrowing honest and the
    message uniform.
    """
    if not isinstance(value, dict):
        fail(message)
    return cast("dict[str, Any]", value)



def main() -> None:
    try:
        data = json.loads(TASKS.read_text(encoding="utf-8"))
        registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(str(error))

    data = require_mapping(data, "tasks.yaml must contain an object")
    registry = require_mapping(registry, "registry.yaml must contain an object")
    if data.get("schema_version") != 1:
        fail("tasks.yaml must use schema_version 1")
    for field in ("preamble", "footer"):
        if not isinstance(data.get(field), str) or not data[field].strip():
            fail(f"tasks.yaml must carry a non-empty {field}")

    results = registry.get("results")
    if not isinstance(results, list):
        fail("registry results must be a list")
    result_ids: set[str] = set()
    landscape_ids: set[str] = set()
    for index, result in enumerate(results):
        result = require_mapping(result, f"registry result {index} must be an object")
        result_id = result.get("id")
        if not isinstance(result_id, str) or not result_id.strip():
            fail(f"registry result {index} id must be a non-empty string")
        result_ids.add(result_id)
        if result_id.startswith("LAND-"):
            landscape_ids.add(result_id)

    tasks = data.get("tasks")
    if not isinstance(tasks, list) or not tasks:
        fail("tasks must be a non-empty list")

    seen: set[str] = set()
    for index, task in enumerate(tasks):
        task = require_mapping(task, f"task {index} must be an object")
        missing = REQUIRED - task.keys()
        if missing:
            fail(f"task {index} missing fields: {sorted(missing)}")

        tid = task["id"]
        if not isinstance(tid, str) or not TASK_ID.fullmatch(tid):
            fail(f"task id must match CT-<n>: {tid!r}")
        if tid in seen:
            fail(f"duplicate task id {tid}")
        seen.add(tid)

        for field in ("title", "rung", "body"):
            if not isinstance(task[field], str) or not task[field].strip():
                fail(f"{tid} must carry a non-empty {field}")
        if not isinstance(task["size"], str) or task["size"] not in SIZES:
            fail(f"{tid} has unknown size {task['size']!r}")
        if not isinstance(task["status"], str) or task["status"] not in STATUSES:
            fail(f"{tid} has unknown status {task['status']!r}")
        if task["heading_level"] not in (2, 3):
            fail(f"{tid} heading_level must be 2 or 3")

        # The badge is what a reader sees; `status` is what tooling reads.
        # They are the same fact and must not disagree.
        badge_done = task["rung"].strip().lower().startswith("done")
        if badge_done != (task["status"] == "DONE"):
            fail(
                f"{tid} rung badge {task['rung']!r} disagrees with "
                f"status {task['status']!r}"
            )

        issue = task.get("issue")
        if issue is not None and not isinstance(issue, int):
            fail(f"{tid} issue must be an integer or absent")

        unknown = sorted(set(RESULT_REF.findall(task["body"])) - result_ids)
        if unknown:
            fail(f"{tid} cites result ids that do not exist: {unknown}")
        unknown = sorted(set(CLAIM_REF.findall(task["body"])) - result_ids)
        if unknown:
            fail(f"{tid} cites result ids that do not exist: {unknown}")
        unknown = sorted(set(LANDSCAPE_REF.findall(task["body"])) - landscape_ids)
        if unknown:
            fail(f"{tid} cites landscape ids that do not exist: {unknown}")

    open_count = sum(task["status"] == "OPEN" for task in tasks)
    print(f"tasks ok: {len(tasks)} recorded, {open_count} open")


if __name__ == "__main__":
    main()
