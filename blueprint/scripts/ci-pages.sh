#!/usr/bin/env bash

set -euo pipefail

cd "$(dirname "$0")/.."

# The Blueprint is its own Lake workspace, so the cache fetched by the root build does not populate
# this workspace's copy of Mathlib.
if [[ "${BLUEPRINT_SKIP_CACHE_GET:-0}" != "1" ]]; then
  lake exe cache get
fi
lake exe vbp build

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
