#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
jq -e '.permitted_axioms | sort == ["Classical.choice", "Quot.sound", "propext"]' \
  comparator.json > /dev/null
if [[ "${CHECK_AXIOMS_SKIP_BUILD:-0}" != "1" ]]; then
  lake build
fi
lake env lean scripts/AxiomAudit.lean
