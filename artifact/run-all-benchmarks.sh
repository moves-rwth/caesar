#!/usr/bin/env bash
set -euo pipefail

cd /root/caesar

echo "Running all Caesar benchmarks from benchmarks.txt..."
fish run-benchmarks.fish
echo "Benchmark run completed. Results are in /root/caesar/benchmark-results.csv."

