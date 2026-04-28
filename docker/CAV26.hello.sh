cd /root/caesar

if [[ -t 1 ]]; then
    bold=$'\033[1m'
    dim=$'\033[2m'
    cyan=$'\033[36m'
    green=$'\033[32m'
    yellow=$'\033[33m'
    reset=$'\033[0m'
else
    bold=
    dim=
    cyan=
    green=
    yellow=
    reset=
fi

heading() {
    printf '\n%s%s%s\n' "$bold$cyan" "$1" "$reset"
}

cmd() {
    printf '  %s%s%s\n' "$green" "$1" "$reset"
}

path() {
    printf '  %s%s%s\n' "$yellow" "$1" "$reset"
}

printf '\n%sWelcome to the Caesar CAV 2026 artifact.%s\n\n' "$bold" "$reset"
printf '%sPaper:%s Caesar: A Deductive Verifier for Probabilistic Programs\n' "$bold" "$reset"
printf '%sCaesar version:%s v4.0.0\n' "$bold" "$reset"

heading "Quick commands"
cmd "artifact/run-smoke.sh"
cmd "artifact/run-model-checking.sh"
cmd "artifact/run-all-benchmarks.sh"
cmd "caesar verify tests/case-studies/zeroconf.heyvl"
cmd "caesar mc --run-storm path --storm-exact --storm-constants bound=4 tests/model-checking/bounded-random-walk.heyvl"
cmd "caesar verify --help"
cmd "storm --version"

heading "Caesar website and docs"
path "https://www.caesarverifier.org/"
path "https://www.caesarverifier.org/docs/"
printf '  %sOnline docs are easier to navigate, but the public website may use Google Analytics.%s\n' "$dim" "$reset"

heading "Offline docs in this container"
path "Markdown: /root/caesar/website/docs/"
path "HTML:     /root/caesar/website/build/index.html"

heading "Project directory"
path "/root/caesar"
printf '\n'

exec bash
