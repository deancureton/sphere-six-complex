#!/usr/bin/env bash

set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tools_root="$project_root/.ci"
lean4export_rev="15f6055e299ad5b89345e533cc2192f4cc00f659"
comparator_rev="3927ad383f208ae977c340a91c48ac9b497d2097"

mkdir -p "$tools_root"

if [[ ! -d "$tools_root/lean4export/.git" ]]; then
  git clone https://github.com/leanprover/lean4export.git "$tools_root/lean4export"
fi
git -C "$tools_root/lean4export" fetch --tags origin
git -C "$tools_root/lean4export" checkout --detach "$lean4export_rev"
cp "$project_root/lean-toolchain" "$tools_root/lean4export/lean-toolchain"
(cd "$tools_root/lean4export" && lake build lean4export)

if [[ ! -d "$tools_root/comparator/.git" ]]; then
  git clone https://github.com/leanprover/comparator.git "$tools_root/comparator"
fi
git -C "$tools_root/comparator" fetch --tags origin
git -C "$tools_root/comparator" checkout --detach "$comparator_rev"
cp "$project_root/lean-toolchain" "$tools_root/comparator/lean-toolchain"
(cd "$tools_root/comparator" && lake update && lake build comparator)
