#!/usr/bin/env bash

set -euo pipefail

cd "$(dirname "$0")/.."

if [[ "${BLUEPRINT_SKIP_CACHE_GET:-0}" != "1" ]]; then
  bash ../scripts/get-mathlib-cache.sh
fi
lake exe vbp build

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
