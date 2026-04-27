# syntax=docker/dockerfile:1.19

# ---- Builder image with the Rust build ----

FROM rust:1-bookworm AS builder

RUN apt-get update && apt-get install -y --no-install-recommends \
    clang \
    cmake \
    git \
    libclang-dev \
    lld \
    llvm-dev \
    pkg-config \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /root/caesar
COPY --exclude=artifact --exclude=docker/CAV26.dockerfile --exclude=docker/CAV26.hello.sh . .

RUN printf "[net]\ngit-fetch-with-cli = true\n" >> "$CARGO_HOME/config.toml"

RUN cargo build --release --workspace

RUN mkdir /result \
    && cp /root/caesar/target/release/caesar /result/caesar \
    && cp /root/caesar/target/release/scooter /result/scooter \
    && rm -rf /root/caesar/target \
    && mkdir -p /root/caesar/target/release \
    && cp /result/scooter /root/caesar/target/release/scooter

# ---- Runtime image ----

FROM debian:bookworm-slim

ENV LC_ALL=C.UTF-8
ENV LANG=C.UTF-8

RUN apt-get update && apt-get install -y --no-install-recommends \
    bash \
    ca-certificates \
    fish \
    git \
    nano \
    vim \
    && rm -rf /var/lib/apt/lists/*

RUN ln -snf /usr/share/zoneinfo/Etc/UTC /etc/localtime \
    && echo "Etc/UTC" > /etc/timezone

COPY --from=builder /root/caesar /root/caesar
COPY --from=builder /result/caesar /usr/local/bin/caesar
COPY --from=builder /result/scooter /usr/local/bin/scooter

RUN mkdir -p /root/caesar/artifact \
    && ln -sf /usr/local/bin/caesar /root/caesar/target/release/caesar \
    && ln -sf /usr/local/bin/scooter /root/caesar/target/release/scooter

COPY artifact/ /root/caesar/artifact/

RUN chmod +x /root/caesar/artifact/run-smoke.sh \
    /root/caesar/artifact/run-all-benchmarks.sh

COPY docker/CAV26.hello.sh /root/caesar/docker/CAV26.hello.sh
COPY artifact/README.md /root/README.md

WORKDIR /root/caesar

CMD ["/bin/bash", "/root/caesar/docker/CAV26.hello.sh"]
