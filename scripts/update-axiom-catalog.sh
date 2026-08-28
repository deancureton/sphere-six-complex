#!/usr/bin/env bash
#
# Generate or check the exact permitted-axiom catalog embedded in ChallengeAxioms.lean.

set -euo pipefail

case "${1:-}" in
  --write|--check) mode="$1" ;;
  *)
    echo "usage: $0 --write|--check" >&2
    exit 2
    ;;
esac

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
allowlist="$project_root/scripts/allowed-axioms.txt"
catalog_source="$project_root/ChallengeAxioms.lean"
begin_marker='/- BEGIN GENERATED AXIOM CATALOG'
end_marker='END GENERATED AXIOM CATALOG -/'

if [[ "$(grep -cFx "$begin_marker" "$catalog_source")" -ne 1 \
    || "$(grep -cFx "$end_marker" "$catalog_source")" -ne 1 ]]; then
  echo "Axiom catalog markers are missing or duplicated in ChallengeAxioms.lean." >&2
  exit 1
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

print_source="$work/PrintAxiomCatalog.lean"
print_output="$work/printed.txt"
catalog="$work/catalog.txt"
candidate="$work/ChallengeAxioms.lean"

{
  echo "import ChallengeAxioms"
  while IFS= read -r line || [[ -n "$line" ]]; do
    [[ -z "$line" || "$line" == \#* ]] && continue
    printf '#eval IO.println "AXIOM-CATALOG:%s"\n' "$line"
    printf '#print %s\n' "$line"
  done < "$allowlist"
  echo '#eval IO.println "AXIOM-CATALOG:END"'
} > "$print_source"

cd "$project_root"
lake env lean -Dpp.proofs=true "$print_source" > "$print_output"

expected_count="$({ grep -v '^[[:space:]]*#' "$allowlist" || true; } \
  | { grep -v '^[[:space:]]*$' || true; } | wc -l | tr -d ' ')"
printed_count="$(grep -c '^AXIOM-CATALOG:' "$print_output")"
if [[ "$printed_count" -ne $((expected_count + 1)) ]]; then
  echo "Lean did not print exactly one catalog block for every permitted constant." >&2
  exit 1
fi

{
  echo "This block is generated from scripts/allowed-axioms.txt by Lean's pretty-printer."
  echo "It is the single human-review surface for every permitted constant and its exact type."
  echo "Do not edit it by hand; run ./scripts/update-axiom-catalog.sh --write."
  echo
  while IFS= read -r line || [[ -n "$line" ]]; do
    if [[ -z "$line" ]]; then
      echo
    elif [[ "$line" == \#* ]]; then
      echo "$line"
    else
      awk -v marker="AXIOM-CATALOG:$line" '
        $0 == marker { printing = 1; next }
        printing && index($0, "AXIOM-CATALOG:") == 1 { exit }
        printing { print }
      ' "$print_output"
    fi
  done < "$allowlist"
} > "$catalog"

if grep -q '⋯' "$catalog"; then
  echo "Lean abbreviated a catalog type; the generated review surface would not be exact." >&2
  exit 1
fi

awk -v begin="$begin_marker" -v end="$end_marker" -v catalog="$catalog" '
  $0 == begin {
    print
    while ((getline line < catalog) > 0) print line
    close(catalog)
    generated = 1
    next
  }
  $0 == end {
    generated = 0
    print
    next
  }
  !generated { print }
' "$catalog_source" > "$candidate"

if [[ "$mode" == "--write" ]]; then
  mv "$candidate" "$catalog_source"
  echo "Updated ChallengeAxioms.lean from scripts/allowed-axioms.txt."
elif ! cmp -s "$catalog_source" "$candidate"; then
  echo "Axiom catalog is stale. Run ./scripts/update-axiom-catalog.sh --write." >&2
  diff -u "$catalog_source" "$candidate" >&2 || true
  exit 1
else
  echo "Axiom catalog check passed."
fi
