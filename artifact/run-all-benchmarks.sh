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

printf '%s%s%s\n' "$bold$cyan" "Running all Caesar benchmark tests from benchmarks.py..." "$reset"
CAESAR_PATH=/usr/local/bin/caesar python3 benchmarks.py | tee benchmark-results.txt
printf '%s%s%s\n' "$green" "Benchmark run completed. Console log is in /root/caesar/benchmark-results.txt; CSV timings are in /root/caesar/benchmark-results.csv." "$reset"
