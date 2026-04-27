#!/usr/bin/env bash
set -euo pipefail

cd /root/caesar

echo "Running Caesar model-checking smoke test with Storm..."
storm --version
caesar mc --run-storm path --storm-exact artifact/model-checking-smoke.heyvl
echo "Model-checking smoke test completed."
