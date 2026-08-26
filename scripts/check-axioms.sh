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
construction_allowlist="$project_root/scripts/allowed-construction-axioms.txt"
cd "$project_root"

targets=(
  "SphereSixComplex.sphere_six_admits_complex_structure"
  "SphereSixComplex.exists_complex_threefold_diffeomorphic_sixSphere"
)

# The implemented-construction cone is audited separately from smooth recognition so changes in
# either trust boundary are reported directly.
construction_targets=(
  "SphereSixComplex.exists_paperGluingData_from_sectionSeven"
  "SphereSixComplex.Geometry.PaperAnalyticData.toPaperGluingData_of_positiveDegree"
  "SphereSixComplex.exists_completedPaperThreefold_of_paperGluingData"
  "SphereSixComplex.Geometry.PaperAnalyticData.sectionSevenStageTopDegreeVanishing_actual"
  "SphereSixComplex.Geometry.PaperAnalyticData.actualStarHasVanKampenData"
)

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

{ grep -v '^[[:space:]]*#' "$allowlist" || true; } \
  | { grep -v '^[[:space:]]*$' || true; } > "$work/allowed-in-order.txt"
jq -r '.permitted_axioms[]' "$project_root/comparator.json" > "$work/comparator-allowed.txt"

if ! cmp -s "$work/allowed-in-order.txt" "$work/comparator-allowed.txt"; then
  echo "Axiom audit FAILED: comparator.json permitted_axioms differs from scripts/allowed-axioms.txt." >&2
  diff -u "$work/allowed-in-order.txt" "$work/comparator-allowed.txt" >&2 || true
  exit 1
fi

lake env lean "$project_root/scripts/ComparatorAxiomClosure.lean" \
  > "$work/comparator-closure.txt"
sort -u "$work/allowed-in-order.txt" > "$work/allowed-sorted.txt"
sort -u "$work/comparator-closure.txt" > "$work/comparator-closure-sorted.txt"

if ! cmp -s "$work/allowed-sorted.txt" "$work/comparator-closure-sorted.txt"; then
  echo "Axiom audit FAILED: Comparator's recursive axiom closure differs from the allowlist." >&2
  diff -u "$work/allowed-sorted.txt" "$work/comparator-closure-sorted.txt" >&2 || true
  exit 1
fi

{
  echo "import SphereSixComplex.Main"
  for target in "${targets[@]}" "${construction_targets[@]}"; do
    echo "#print axioms $target"
  done
} > "$work/PrintAxioms.lean"

if [[ -z "${CHECK_AXIOMS_SKIP_BUILD:-}" ]]; then
  lake build SphereSixComplex.Main >/dev/null
fi
lake env lean "$work/PrintAxioms.lean" > "$work/out.txt"

# `#print axioms` prints one bracketed comma-separated list per target, wrapped over several
# lines; a target with no dependencies prints "does not depend on any axioms" and no list.
# Each `#print axioms` block names its own declaration, so parse by name rather than by position:
# a target that depends on no axioms prints "does not depend on any axioms" and contributes no
# bracketed list at all, which would silently shift every later cone if positions were used.
tr '\n' ' ' < "$work/out.txt" \
  | { grep -o "'[^']*' depends on axioms: \[[^]]*\]" || true; } \
  | sed "s/^'//; s/' depends on axioms: \[/ /; s/\]//" > "$work/pairs.txt"

# Collect the axioms of the named targets, one target per line of "$1".
collect_for() {
  local names="$1"
  while read -r name; do
    [[ -z "$name" ]] && continue
    { grep -F "$name " "$work/pairs.txt" || true; } | sed "s/^$name //"
  done < "$names" | tr ',' '\n' | tr -d ' ' | { grep -v '^$' || true; } | sort -u
}

printf '%s\n' "${targets[@]}" > "$work/final-names.txt"
printf '%s\n' "${construction_targets[@]}" > "$work/construction-names.txt"
collect_for "$work/final-names.txt" > "$work/found.txt"
collect_for "$work/construction-names.txt" > "$work/construction.txt"

# A target that printed nothing at all means the name did not resolve; fail loudly rather than
# silently auditing an empty cone.
for target in "${targets[@]}" "${construction_targets[@]}"; do
  if ! grep -q "^${target} " "$work/pairs.txt" \
      && ! grep -qF "'${target}' does not depend on any axioms" "$work/out.txt"; then
    echo "Axiom audit FAILED: no '#print axioms' output for ${target}." >&2
    echo "The name may have been renamed or removed; update scripts/check-axioms.sh." >&2
    exit 1
  fi
done

# `|| true`: an allowlist that is empty or all comments makes the pipeline exit under `pipefail`.
{ grep -v '^[[:space:]]*#' "$allowlist" || true; } | { grep -v '^[[:space:]]*$' || true; } \
  | sort -u > "$work/allowed.txt"

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

# The construction cone is a separate ratchet: it fails only on constants outside its own list, so
# a new `established*` axiom cannot appear unnoticed while the final cone is still masked by
# `sorry`.  Deleting a line as its axiom is discharged is the point; this file should only shrink.
{ grep -v '^[[:space:]]*#' "$construction_allowlist" || true; } \
  | { grep -v '^[[:space:]]*$' || true; } | sort -u > "$work/construction-allowed.txt"

if ! extra="$(comm -23 "$work/construction.txt" "$work/construction-allowed.txt")" \
    || [[ -n "$extra" ]]; then
  echo >&2
  echo "Axiom audit FAILED: the construction depends on constants outside its allowlist:" >&2
  echo "$extra" | sed 's/^/  /' >&2
  echo >&2
  echo "Either prove them, or add them to scripts/allowed-construction-axioms.txt with a" >&2
  echo "justification." >&2
  exit 1
fi

echo
echo "Construction audit passed. The construction depends on $(wc -l < "$work/construction.txt" \
  | tr -d ' ') constants:"
sed 's/^/  /' "$work/construction.txt"
