#!/usr/bin/env bash
set -euo pipefail

cd /root/caesar

echo "Running Caesar model-checking smoke test with Storm..."
storm_version="$(storm --version)"
printf '%s\n' "${storm_version%%$'\n'*}"

run_and_expect() {
    local description="$1"
    local expected="$2"
    shift 2

    echo
    echo "${description}"
    local output
    output="$("$@" 2>&1)"
    printf '%s\n' "$output"
    if [[ "$output" != *"$expected"* ]]; then
        echo "Expected output to contain: $expected" >&2
        exit 1
    fi
}

run_and_expect \
    "Bounded random-walk reachability probability." \
    "0.375" \
    caesar mc --run-storm path --storm-exact --storm-constants bound=4 tests/model-checking/bounded-random-walk.heyvl

run_and_expect \
    "Bounded loop expected runtime from the condand benchmark." \
    "2.5" \
    caesar mc --run-storm path --storm-exact --jani-skip-quant-pre --storm-constants init_n=2,init_m=2 tests/model-checking/bounded-condand-runtime.heyvl

run_and_expect \
    "Bounded loop expected runtime from the linear01 benchmark." \
    "19/9" \
    caesar mc --run-storm path --storm-exact --jani-skip-quant-pre --storm-constants init_x=4 tests/model-checking/bounded-linear-runtime.heyvl

run_and_expect \
    "Crowds-style bounded anonymity probability." \
    "0.73728" \
    caesar mc --run-storm path --storm-exact --storm-constants messages=5,threshold=1 tests/model-checking/crowds-anonymity.heyvl

run_and_expect \
    "Herman-style bounded token-ring stabilization probability." \
    "0.9375" \
    caesar mc --run-storm path --storm-exact --storm-constants rounds=2 tests/model-checking/herman-token-ring.heyvl

run_and_expect \
    "Bayesian-network style noisy-OR model with a fixed observation target." \
    "130307/160000" \
    caesar mc --run-storm path --storm-exact --jani-skip-quant-pre --storm-constants what_n3=true tests/model-checking/noisy-or-network.heyvl

run_and_expect \
    "Bounded retransmission send-packet model with fixed packet and retry counts." \
    "1999999/1000000000000" \
    caesar mc --run-storm path --storm-exact --jani-skip-quant-pre --storm-constants packets=2,maxTries=3 tests/case-studies/brp-send-packet.heyvl

echo "Model-checking smoke test completed."
