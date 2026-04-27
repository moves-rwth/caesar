#!/usr/bin/env bash
set -euo pipefail

cd /root/caesar

echo "Running all Caesar benchmark tests from benchmarks.py..."
CAESAR_PATH=/usr/local/bin/caesar python3 benchmarks.py | tee benchmark-results.txt
echo "Benchmark run completed. Results are in /root/caesar/benchmark-results.txt."
