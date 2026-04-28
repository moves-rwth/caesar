#!/usr/bin/env bash
set -euo pipefail

cd /root/caesar

if [[ -t 1 ]]; then
    bold=$'\033[1m'
    green=$'\033[32m'
    cyan=$'\033[36m'
    reset=$'\033[0m'
else
    bold=
    green=
    cyan=
    reset=
fi

printf '%s%s%s\n' "$bold$cyan" "Running Caesar smoke test..." "$reset"
caesar verify --timeout 60 --mem 10000 tests/case-studies/zeroconf.heyvl
printf '%s%s%s\n' "$green" "Smoke test completed." "$reset"
