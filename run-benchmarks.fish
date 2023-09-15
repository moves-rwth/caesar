cd (dirname (status -f))

if type -q cargo
    echo Building the benchmark tool...
    cargo build --release -p scooter -q; or exit 1
end

echo Timeout: 60s. Memory limit: 10000 MB.

cat benchmarks.txt | target/release/scooter --timeout 60 --mem 10000
