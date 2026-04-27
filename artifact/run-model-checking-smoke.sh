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
    "Finite Markov chain with exact expected reward." \
    "2097151/2097152" \
    caesar mc --run-storm path --storm-exact tests/model-checking/finite-geometric.heyvl

run_and_expect \
    "Parametric infinite-state Markov chain with constants and a state limit." \
    "0.9990234375" \
    caesar mc --run-storm path --storm-constants init_c=5 --storm-state-limit 100 tests/model-checking/parametric-geometric.heyvl

run_and_expect \
    "Markov decision process from demonic nondeterminism." \
    "0" \
    caesar mc --run-storm path --storm-exact tests/model-checking/demonic-choice.heyvl

run_and_expect \
    "Bayesian-network style noisy-OR model with a fixed observation target." \
    "130307/160000" \
    caesar mc --run-storm path --storm-exact --jani-skip-quant-pre --storm-constants what_n3=true tests/model-checking/noisy-or-network.heyvl

run_and_expect \
    "Bounded retransmission send-packet model with fixed packet and retry counts." \
    "1999999/1000000000000" \
    caesar mc --run-storm path --storm-exact --jani-skip-quant-pre --storm-constants packets=2,maxTries=3 tests/case-studies/brp-send-packet.heyvl

echo "Model-checking smoke test completed."
