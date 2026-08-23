#!/usr/bin/env bash

set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
comparator_root="$project_root/.ci/comparator"
lean4export_root="$project_root/.ci/lean4export"

if [[ ! -x "$comparator_root/.lake/build/bin/comparator" ]]; then
  echo "Comparator is not built. Run ./scripts/setup-comparator.sh first." >&2
  exit 1
fi

if [[ "$(uname -s)" == "Darwin" ]]; then
  export COMPARATOR_LANDRUN="$comparator_root/scripts/fake-landrun.sh"
  echo "Warning: fake-landrun checks functionality only; run real Landrun on Linux for isolation." >&2
fi

export COMPARATOR_LEAN4EXPORT="$lean4export_root/.lake/build/bin/lean4export"
cd "$project_root"
lake env "$comparator_root/.lake/build/bin/comparator" comparator.json
