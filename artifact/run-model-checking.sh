#!/usr/bin/env bash
set -euo pipefail

cd /root/caesar

if [[ -t 1 ]]; then
    bold=$'\033[1m'
    green=$'\033[32m'
    red=$'\033[31m'
    cyan=$'\033[36m'
    yellow=$'\033[33m'
    reset=$'\033[0m'
else
    bold=
    green=
    red=
    cyan=
    yellow=
    reset=
fi

printf '%s%s%s\n' "$bold$cyan" "Running Caesar model checking with Storm..." "$reset"
storm_version="$(storm --version)"
printf '%sStorm:%s %s\n' "$bold" "$reset" "${storm_version%%$'\n'*}"

run_and_expect() {
    local description="$1"
    local expected="$2"
    shift 2

    echo
    printf '%s%s%s\n' "$bold$cyan" "${description}" "$reset"
    local output
    output="$("$@" 2>&1)"
    printf '%s\n' "$output"
    if [[ "$output" != *"$expected"* ]]; then
        printf '%sExpected output to contain:%s %s\n' "$red" "$reset" "$expected" >&2
        exit 1
    fi
    printf '%sMatched expected output:%s %s\n' "$green" "$reset" "$expected"
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

printf '%s%s%s\n' "$green" "Model checking completed." "$reset"
