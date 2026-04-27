#!/usr/bin/env bash
set -euo pipefail

cd /root/caesar

echo "Running Caesar smoke test..."
caesar verify --timeout 60 --mem 10000 tests/case-studies/zeroconf.heyvl
echo "Smoke test completed."

