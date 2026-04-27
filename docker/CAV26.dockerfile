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
COPY Cargo.toml Cargo.lock build.rs ./
COPY src/ src/
COPY jani/ jani/
COPY z3rro/ z3rro/

RUN sed -i '/"scooter"/d' Cargo.toml

RUN printf "[net]\ngit-fetch-with-cli = true\n" >> "$CARGO_HOME/config.toml"

RUN cargo build --release -p caesar

RUN mkdir /result \
    && cp /root/caesar/target/release/caesar /result/caesar \
    && rm -rf /root/caesar/target

# ---- Documentation build ----

FROM node:22-bookworm-slim AS docs

WORKDIR /root/caesar/website
COPY website/package.json website/yarn.lock ./
RUN corepack enable \
    && corepack prepare yarn@1.22.22 --activate \
    && yarn install --frozen-lockfile

COPY website/ ./
RUN yarn build

# ---- Storm binary/runtime extraction ----

# Storm's GitHub releases currently publish source archives, not standalone
# Linux binaries. The official Storm Docker image is built from that release
# source and provides native linux/amd64 and linux/arm64 binaries. Use it only
# as a binary source stage so the final artifact does not inherit the full
# multi-GB Storm image.
FROM movesrwth/storm:stable AS storm

RUN mkdir -p /storm-root \
    && mkdir -p /storm-root/usr/local/bin \
    && mkdir -p /storm-root/usr/local/storm-libs \
    && mkdir -p /storm-root/opt/gurobi/linux/lib \
    && cp -L /usr/local/bin/storm /storm-root/usr/local/bin/storm \
    && cp -a --parents /usr/local/lib/storm /storm-root/ \
    && cp -L /opt/gurobi/linux/lib/libgurobi130.so /storm-root/opt/gurobi/linux/lib/libgurobi130.so \
    && ldd /usr/local/bin/storm \
        | awk '{ print $3 }' \
        | grep '^/' \
        | xargs -r -I '{}' cp -L '{}' /storm-root/usr/local/storm-libs/

# ---- Runtime image ----

FROM ubuntu:25.10

ENV LC_ALL=C.UTF-8
ENV LANG=C.UTF-8
ENV LD_LIBRARY_PATH=/usr/local/storm-libs:/usr/local/lib/storm:/usr/local/lib/storm/resources:/opt/gurobi/linux/lib

RUN apt-get update && apt-get install -y --no-install-recommends \
    bash \
    ca-certificates \
    git \
    nano \
    python3 \
    vim \
    && rm -rf /var/lib/apt/lists/*

RUN ln -snf /usr/share/zoneinfo/Etc/UTC /etc/localtime \
    && echo "Etc/UTC" > /etc/timezone

COPY . /root/caesar
COPY --from=storm /storm-root/ /
COPY --from=builder /result/caesar /usr/local/bin/caesar
COPY --from=docs /root/caesar/website/build /root/caesar/website/build

RUN mkdir -p /root/caesar/artifact /root/caesar/target/release \
    && ln -sf /usr/local/bin/caesar /root/caesar/target/release/caesar

COPY artifact/ /root/caesar/artifact/

RUN chmod +x /root/caesar/artifact/run-smoke.sh \
    /root/caesar/artifact/run-model-checking-smoke.sh \
    /root/caesar/artifact/run-all-benchmarks.sh

COPY docker/CAV26.hello.sh /root/caesar/docker/CAV26.hello.sh
COPY artifact/README.md /root/README.md

WORKDIR /root/caesar

CMD ["/bin/bash", "/root/caesar/docker/CAV26.hello.sh"]
