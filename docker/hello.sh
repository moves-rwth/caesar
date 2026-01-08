cd /root/caesar

echo
echo
echo "Welcome to Caesar's Docker container."
echo
echo "-------------------------------"
echo ESOP26 Artifact Evaluation Guide
echo
echo     See ESOP26.md
echo
echo "-------------------------------"
echo
echo "You are now in the project's main directory."
echo
echo "The slicing benchmarks can be run with"
echo "    cd slicing-benchmarks; fish all-benchmarks.fish"
echo
echo "You can run slicing on individual files, e.g."
echo "    caesar verify slicing-benchmarks/navarro20/example4_5.heyvl --slice-verify --slice-verify-via mus"
echo
echo "For usage information, run"
echo "    caesar verify --help"
echo
echo "Online documentation is available on"
echo "    https://www.caesarverifier.org/"

exec bash
