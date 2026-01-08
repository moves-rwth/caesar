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
echo "Running benchmarks in error-witnessing.txt... (Table 5)"
cat error-witnessing.txt | $scooter_cmd --timeout 30 > result-error-witnessing.csv

echo
echo "-------------------------------"
echo "Running benchmarks in verification-preserving.txt... (Table 6)"
cat verification-preserving.txt | $scooter_cmd --timeout 30 > result-verification-preserving.csv

echo
echo "-------------------------------"
echo "Running benchmarks in verification-witnessing.txt... (Table 6)"
cat verification-witnessing.txt | $scooter_cmd --timeout 30 > result-verification-witnessing.csv

echo
echo "-------------------------------"
echo "Running benchmarks in verifying.txt... (Figure 23, Figure 24)"
cat verifying.txt | $scooter_cmd --timeout 30 > result-verifying.csv

echo
echo "-------------------------------"
echo "Running benchmarks in verifying-subset.txt... (Figure 14)"
cat verifying-subset.txt | $scooter_cmd --timeout 30 > result-verifying-subset.csv


echo
echo "-------------------------------"
echo "Generating plots (Figure 14, Figure 23, Figure 24)."
# Replace timeouts by a large value (30000) for the plots
sed -e 's/-/30000/g' result-verifying.csv > plots/result-verifying-plot.csv
sed -e 's/-/30000/g' result-verifying-subset.csv |
# Add an ID to each row to generate the bar plot (https://stackoverflow.com/a/30530523)
    awk -F',' -v OFS=',' ' 
        NR == 1 {print "id", $0; next}
        {print (NR-1), $0}
    ' > plots/result-verifying-subset-plot.csv
latexmk plots/plots.tex -lualatex -outdir=plots -interaction=nonstopmode --halt-on-error -file-line-error > plots/buildplots.log
cp plots/plots.pdf plots.pdf

echo
echo "-------------------------------"
echo "All benchmarks completed."
echo "Results are in result-*.csv files."
echo "Plots are in plots.pdf"