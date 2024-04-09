# ---- Builder image with the Rust build ----
FROM rust:latest as builder

# install required dependencies to build z3.rs...
RUN apt-get update && apt-get install -y cmake llvm-dev libclang-dev clang

WORKDIR /root/caesar
COPY . .

# Use git CLI to fetch crates (avoid memory issues in QEMU environments)
# see https://github.com/rust-lang/cargo/issues/10583
RUN printf "[net]\ngit-fetch-with-cli = true" >> "$CARGO_HOME/config.toml"

RUN cargo build --verbose --release

# ---- Building the final Docker image ----
FROM gcr.io/distroless/cc-debian12:latest

COPY --from=builder /root/caesar/target/release/caesar /caesar

ENTRYPOINT ["./caesar"]
