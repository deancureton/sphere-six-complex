#!/usr/bin/env bash
set -euo pipefail

MATHLIB_NO_CACHE_ON_UPDATE=1 lake env true

project_toolchain="$(tr -d '[:space:]' < lean-toolchain)"
mathlib_toolchain="$(tr -d '[:space:]' < .lake/packages/mathlib/lean-toolchain)"
if [[ "$project_toolchain" == "$mathlib_toolchain" ]]; then
  lake exe cache get
else
  echo "Mathlib cache uses $mathlib_toolchain; building from source with $project_toolchain."
fi
