#!/usr/bin/env bash
# Reproduce the FormalizedFormalLogic/Foundation pin used by the Logic layer
# (BY-013, BY-016, BY-027 and Gödel II companion). Correlated coverage risk:
# one Foundation pin supplies four survey-facing incompleteness aliases.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Read the pin from the resolved manifest rather than repeating it here: a
# hard-coded copy silently became a false claim across the v4.33.0 migration.
PIN="$(python3 -c 'import json;print(next(p["rev"] for p in json.load(open("lake-manifest.json"))["packages"] if p["name"]=="Foundation"))')"
if [[ -z "${PIN}" ]]; then
  echo "could not read the Foundation revision from lake-manifest.json" >&2
  exit 1
fi
echo "Reproducing Foundation pin ${PIN} via atlas Lake dependency..."
echo "Modules exercised by AISafetyAtlas.Logic:"
echo "  Foundation.FirstOrder.Incompleteness.{First,Second,Tarski,Löb}"

lake build AISafetyAtlas.Logic

echo "Foundation Logic surface built successfully against the pinned dependency."
