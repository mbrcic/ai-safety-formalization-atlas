"""Shared setup for the tests.

Many tests run a validator as a child process and read what it prints with
``encoding="utf-8"`` (tests/test_text_io_explicit.py requires that).  The child
is Python, and Python encodes its standard streams by the platform default
unless told otherwise: on Windows that is a legacy code page, so a validator
that printed a dash or an arrow produced bytes the parent could not decode.
``agent_gate.sh`` exports the same variable; setting it here makes a bare
``pytest tests/`` behave the same way as the gate.
"""

from __future__ import annotations

import os

os.environ["PYTHONIOENCODING"] = "utf-8"
