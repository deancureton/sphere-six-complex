#!/usr/bin/env bash

set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tools_root="$project_root/.ci"
lean4export_rev="b18d673bd29b476466a51a3be1012df2ed322b10"
comparator_rev="8d84e678dc9954b12db91f7f3167a169b309e0c8"
project_toolchain_before="$(< "$project_root/lean-toolchain")"

verify_project_toolchain() {
  if [[ "$(< "$project_root/lean-toolchain")" != "$project_toolchain_before" ]]; then
    echo "Comparator setup changed the project lean-toolchain; aborting." >&2
    return 1
  fi
}
trap verify_project_toolchain EXIT

mkdir -p "$tools_root"

if [[ ! -d "$tools_root/lean4export/.git" ]]; then
  git clone https://github.com/leanprover/lean4export.git "$tools_root/lean4export"
fi
git -C "$tools_root/lean4export" restore --source=HEAD -- lean-toolchain
git -C "$tools_root/lean4export" fetch --tags origin
git -C "$tools_root/lean4export" checkout --detach "$lean4export_rev"
cp "$project_root/lean-toolchain" "$tools_root/lean4export/lean-toolchain"
(cd "$tools_root/lean4export" && lake build lean4export)

if [[ ! -d "$tools_root/comparator/.git" ]]; then
  git clone https://github.com/leanprover/comparator.git "$tools_root/comparator"
fi
git -C "$tools_root/comparator" restore --source=HEAD -- lean-toolchain lake-manifest.json
git -C "$tools_root/comparator" fetch --tags origin
git -C "$tools_root/comparator" checkout --detach "$comparator_rev"
(cd "$tools_root/comparator" && lake update && lake build comparator)
