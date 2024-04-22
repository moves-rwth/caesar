# ---- Base builder image with rust ----
FROM --platform=$BUILDPLATFORM rust:latest AS rust-builder

# install required dependencies to build z3.rs...
RUN apt-get update && apt-get install -y cmake llvm-dev libclang-dev clang

WORKDIR /root/caesar
COPY . .

# Use git CLI to fetch crates (avoid memory issues in QEMU environments)
# see https://github.com/rust-lang/cargo/issues/10583
RUN printf "[net]\ngit-fetch-with-cli = true" >> "$CARGO_HOME/config.toml"

### Platform-specific configuration ###
# ---- [amd64] Platform-specific setup for cross-compilation ----
FROM --platform=$BUILDPLATFORM rust-builder AS builder-linux-amd64

ENV CAESAR_ARCH="x86_64-unknown-linux-gnu"

RUN apt-get install -y g++-x86-64-linux-gnu libc-dev-amd64-cross

RUN rustup target add x86_64-unknown-linux-gnu

ENV CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER=x86_64-linux-gnu-gcc \
    CC_x86_64_unknown_linux_gnu=x86_64-linux-gnu-gcc \
    CXX_x86_64_unknown_linux_gnu=x86_64-linux-gnu-g++

# ---- [arm64] Platform-specific setup for cross-compilation ----
FROM --platform=$BUILDPLATFORM rust-builder AS builder-linux-arm64 

ENV CAESAR_ARCH="aarch64-unknown-linux-gnu"

RUN apt-get install -y g++-aarch64-linux-gnu libc-dev-arm64-cross

RUN rustup target add aarch64-unknown-linux-gnu

ENV CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER=aarch64-linux-gnu-gcc \
    CC_aarch64_unknown_linux_gnu=aarch64-linux-gnu-gcc \
    CXX_aarch64_unknown_linux_gnu=aarch64-linux-gnu-g++

# ---- Perform build using target-specific builder image ----
FROM --platform=$BUILDPLATFORM builder-$TARGETOS-$TARGETARCH as builder

RUN cargo build --verbose --release --target ${CAESAR_ARCH}

RUN cp target/${CAESAR_ARCH}/release/caesar target/release/caesar

# ---- Building the final Docker image ----
FROM gcr.io/distroless/cc-debian12:latest

COPY --from=builder /root/caesar/target/release/caesar /caesar

ENTRYPOINT ["./caesar"]
