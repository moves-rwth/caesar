cd /root/caesar

echo
echo "Welcome to the Caesar CAV 2026 artifact."
echo
echo "Paper: Caesar: A Deductive Verifier for Probabilistic Programs"
echo "Caesar version: v4.0.0"
echo
echo "Quick commands:"
echo "  artifact/run-smoke.sh"
echo "  artifact/run-all-benchmarks.sh"
echo "  caesar verify tests/case-studies/zeroconf.heyvl"
echo "  caesar verify --help"
echo
echo "Artifact guide:"
echo "  /root/README.md"
echo
echo "Caesar website and docs:"
echo "  https://www.caesarverifier.org/"
echo "  https://www.caesarverifier.org/docs/"
echo "  Online docs are easier to navigate, but the public website may use Google Analytics."
echo
echo "Offline docs in this container:"
echo "  Markdown: /root/caesar/website/docs/"
echo "  HTML:     /root/caesar/website/build/index.html"
echo
echo "Project directory:"
echo "  /root/caesar"
echo

exec bash
