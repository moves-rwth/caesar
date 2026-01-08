# ---- Base builder image with rust ----
FROM rust:1-bookworm AS builder

# install required dependencies to build z3.rs...
RUN apt-get update && apt-get install -y cmake llvm-dev libclang-dev clang lld

WORKDIR /root/caesar
COPY . .

# Use git CLI to fetch crates (avoid memory issues in QEMU environments)
# see https://github.com/rust-lang/cargo/issues/10583
RUN printf "[net]\ngit-fetch-with-cli = true" >> "$CARGO_HOME/config.toml"

# Now do the build
RUN cargo build --verbose --release --workspace

# because .dockerignore files don't work when copying between build stages,
# we copy the binaries before removing the target directory. then we recreate
# it again with just the binaries. this saves about 10 gigabytes in the final Docker image.
RUN mkdir /result && \
    cp /root/caesar/target/release/caesar /result/caesar && \
    cp /root/caesar/target/release/scooter /result/scooter && \
    rm -rf /root/caesar/target

# ---- Building the final Docker image ----
FROM debian:bookworm-slim

# setup caesar environment
COPY --from=builder /root/caesar /root/caesar
COPY --from=builder /result/caesar /usr/local/bin/caesar
COPY --from=builder /result/scooter /usr/local/bin/scooter
RUN mkdir -p /root/caesar/target/release && ln -s /usr/local/bin/caesar /root/caesar/target/release/caesar && ln -s /usr/local/bin/scooter /root/caesar/target/release/scooter

# install some helpers, texlive for re-generating figures
RUN apt-get update && apt-get install -y fish vim nano wget texlive texlive-pictures latexmk && rm -rf /var/lib/apt/lists/*

# entry point
WORKDIR /root/caesar
CMD ["/bin/bash", "/root/caesar/docker/hello.sh"]
