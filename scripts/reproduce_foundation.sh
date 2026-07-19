#!/usr/bin/env bash
# Reproduce the FormalizedFormalLogic/Foundation pin used by the Logic layer
# (BY-013, BY-016, BY-027 and Gödel II companion). Correlated coverage risk:
# one Foundation pin supplies four survey-facing incompleteness aliases.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

PIN="b47cf447255addf88a5d72781d0d29641948eb6e"
echo "Reproducing Foundation pin ${PIN} via atlas Lake dependency..."
echo "Modules exercised by AISafetyAtlas.Logic:"
echo "  Foundation.FirstOrder.Incompleteness.{First,Second,Tarski,Löb}"

lake build AISafetyAtlas.Logic

echo "Foundation Logic surface built successfully against the pinned dependency."
