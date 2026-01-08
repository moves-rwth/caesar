cd (dirname (status -f))

if command -v scooter &> /dev/null
    set scooter_cmd scooter
else if command -v cargo &> /dev/null
    echo "Building the benchmark tool..."
    cargo build --release -p scooter -q
    or exit 1
    set scooter_cmd target/release/scooter
else
    echo "Error: Neither scooter nor cargo is available" >&2
    exit 1
end

echo "Running all benchmarks with timeout 30s each..."
echo "Generating results in result-*.csv files."
echo "On an Apple M1 Pro, this finishes in < 10 minutes."

echo
echo "-------------------------------"
echo "Running benchmarks in error-preserving.txt... (Figure 14, Table 5)"
cat error-preserving.txt | $scooter_cmd --timeout 30 | column -t -s ',' > result-error-preserving.csv

echo
echo "-------------------------------"
echo "Running benchmarks in verification-preserving.txt... (Table 6)"
cat verification-preserving.txt | $scooter_cmd --timeout 30 | column -t -s ',' > result-verification-preserving.csv

echo
echo "-------------------------------"
echo "Running benchmarks in verification-witnessing.txt... (Table 6)"
cat verification-witnessing.txt | $scooter_cmd --timeout 30 | column -t -s ',' > result-verification-witnessing.csv

echo
echo "-------------------------------"
echo "Running benchmarks in verifying.txt... (Figure 23, Figure 24)"
cat verifying.txt | $scooter_cmd --timeout 30 | column -t -s ',' > result-verifying.csv

echo
echo "-------------------------------"
echo "All benchmarks completed."
echo "Results are in result-*.csv files."
