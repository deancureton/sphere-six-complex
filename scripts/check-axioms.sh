#!/usr/bin/env bash
#
# Trust gate: assert that the audited dependency cones exactly match their declared allowlists.
#
# Runs `#print axioms` on the project endpoints and fails if a constant is missing from an
# allowlist or remains there after it is no longer reached. Add a line only together with a
# written justification of the new trust boundary; remove it when the dependency is discharged.
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

# The *implemented-construction* cone.  While `exists_paperGluingData` is a placeholder the final
# cone above cannot see any construction axiom, because `sorry` short-circuits axiom tracking; this
# second list restores what is visible today.
#
# It is deliberately a partial cone, not the whole construction.  No production
# `SectionSevenPositiveDegreeHomologyAssembly` witness exists yet, so the assembly `H` contributes
# nothing here; when one lands it should be added as a target.  What this does pin is the assembly
# path, the recognition step, and the two obligations already discharged, so that a new axiom in
# any of them cannot pass unnoticed.
construction_targets=(
  "SphereSixComplex.Geometry.PaperAnalyticData.toPaperGluingData_of_positiveDegree"
  "SphereSixComplex.exists_completedPaperThreefold_of_paperGluingData"
  "SphereSixComplex.completedPaperThreefold_smoothRecognition"
  "SphereSixComplex.Geometry.PaperAnalyticData.sectionSevenStageTopDegreeVanishing_actual"
  "SphereSixComplex.Geometry.PaperAnalyticData.actualStarHasVanKampenData"
)

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

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

if ! stale="$(comm -13 "$work/found.txt" "$work/allowed.txt")" || [[ -n "$stale" ]]; then
  echo "Axiom audit FAILED: the final allowlist contains constants not reached by the final" >&2
  echo "theorem:" >&2
  echo "$stale" | sed 's/^/  /' >&2
  echo >&2
  echo "Remove them from scripts/allowed-axioms.txt; the allowlist should shrink as" >&2
  echo "dependencies are discharged." >&2
  exit 1
fi

echo "Axiom audit passed. The final theorem depends on:"
sed 's/^/  /' "$work/found.txt"

if grep -qx 'sorryAx' "$work/found.txt"; then
  echo
  echo "Note: sorryAx is still present, so the development is not yet complete."
fi

# The construction cone is a separate exact ratchet, so a new `established*` axiom cannot appear
# unnoticed while the final cone is still masked by `sorry`, and a discharged dependency must be
# removed from its list. This file should only shrink.
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

if ! stale="$(comm -13 "$work/construction.txt" "$work/construction-allowed.txt")" \
    || [[ -n "$stale" ]]; then
  echo >&2
  echo "Axiom audit FAILED: the construction allowlist contains constants not reached by the" >&2
  echo "implemented-construction targets:" >&2
  echo "$stale" | sed 's/^/  /' >&2
  echo >&2
  echo "Remove them from scripts/allowed-construction-axioms.txt; the allowlist should shrink" >&2
  echo "as dependencies are discharged." >&2
  exit 1
fi

echo
echo "Construction audit passed. The construction depends on $(wc -l < "$work/construction.txt" \
  | tr -d ' ') constants:"
sed 's/^/  /' "$work/construction.txt"
