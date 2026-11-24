#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
export PYTHONDONTWRITEBYTECODE=1
binary=${LOL_BIN:-$(cabal list-bin exe:lol)}
for suite in test/v1_*.py; do
    python3 test/resources.py --rss-mib 1800 --seconds 90 -- python3 "$suite" "$binary"
done
export LOL_EDITOR_TEST_BIN="$binary"
python3 test/resources.py --rss-mib 900 --seconds 55 -- node --test editors/vscode/test/client.test.js
