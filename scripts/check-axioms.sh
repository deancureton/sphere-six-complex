#!/usr/bin/env bash
#
# Trust gate: assert that the final theorem depends on nothing beyond the declared allowlist.
#
# Runs `#print axioms` on the project endpoint and on the Comparator wrapper, and fails if any
# constant appears that is not listed in `scripts/allowed-axioms.txt`.  Add a line to that file
# only together with a written justification of the new trust boundary.
#
# Usage: ./scripts/check-axioms.sh
#
# Set CHECK_AXIOMS_SKIP_BUILD=1 to reuse an existing build instead of running `lake build`.

set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
allowlist="$project_root/scripts/allowed-axioms.txt"
cd "$project_root"

targets=(
  "SphereSixComplex.sphere_six_admits_complex_structure"
  "SphereSixComplex.exists_complex_threefold_diffeomorphic_sixSphere"
)

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

{
  echo "import SphereSixComplex.Final"
  for target in "${targets[@]}"; do
    echo "#print axioms $target"
  done
} > "$work/PrintAxioms.lean"

if [[ -z "${CHECK_AXIOMS_SKIP_BUILD:-}" ]]; then
  lake build SphereSixComplex.Final >/dev/null
fi
lake env lean "$work/PrintAxioms.lean" > "$work/out.txt"

# `#print axioms` prints one bracketed comma-separated list per target, wrapped over several
# lines; a target with no dependencies prints "does not depend on any axioms" and no list.
tr '\n' ' ' < "$work/out.txt" \
  | grep -o 'depends on axioms: \[[^]]*\]' \
  | sed 's/depends on axioms: \[//; s/\]//' \
  | tr ',' '\n' \
  | tr -d ' ' \
  | grep -v '^$' \
  | sort -u > "$work/found.txt"

grep -v '^[[:space:]]*#' "$allowlist" | grep -v '^[[:space:]]*$' | sort -u > "$work/allowed.txt"

if ! extra="$(comm -23 "$work/found.txt" "$work/allowed.txt")" || [[ -n "$extra" ]]; then
  echo "Axiom audit FAILED: the final theorem depends on constants outside the allowlist:" >&2
  echo "$extra" | sed 's/^/  /' >&2
  echo >&2
  echo "Either prove them, or add them to scripts/allowed-axioms.txt with a justification." >&2
  exit 1
fi

echo "Axiom audit passed. The final theorem depends on:"
sed 's/^/  /' "$work/found.txt"

if grep -qx 'sorryAx' "$work/found.txt"; then
  echo
  echo "Note: sorryAx is still present, so the development is not yet complete."
fi
