# ---- Builder image with the Rust build ----

FROM rust:1.67 as builder

# install required dependencies to build z3.rs...
RUN apt-get update && apt-get install -y cmake llvm-dev libclang-dev clang

WORKDIR /root/caesar
COPY . .

# Use git CLI to fetch crates (avoid memory issues in QEMU environments)
# see https://github.com/rust-lang/cargo/issues/10583
RUN printf "[net]\ngit-fetch-with-cli = true" >> "$CARGO_HOME/config.toml"

RUN cargo build --release --workspace

# because .dockerignore files don't work when copying between build stages,
# we copy the binaries before removing the target directory. then we recreate
# it again with just the binaries. this saves about 10 gigabytes in the final Docker image.
RUN mkdir /result && \
    cp /root/caesar/target/release/caesar /result/caesar && \
    cp /root/caesar/target/release/scooter /result/scooter && \
    rm -rf /root/caesar/target

# ---- Building the final Docker image ----

FROM debian:bullseye-slim

RUN apt-get update && apt-get install -y fish && rm -rf /var/lib/apt/lists/*

COPY --from=builder /root/caesar /root/caesar
COPY --from=builder /result/caesar /usr/local/bin/caesar
COPY --from=builder /result/scooter /root/caesar/target/release/scooter
RUN ln -s /usr/local/bin/caesar /root/caesar/target/release/caesar

# ---- Setup for pgcl2heyvl ----

ENV LC_ALL=C.UTF-8
ENV LANG=C.UTF-8

# Setup timezone
RUN ln -snf /usr/share/zoneinfo/Etc/UTC /etc/localtime \
    && echo "Etc/UTC" > /etc/timezone

RUN apt-get update && apt-get install -y git curl python3 python3-distutils python3-apt
# setup git so we can use it with poetry later
RUN git config --global user.name "Your Name" && git config --global user.email "you@example.com"
RUN curl -sSL https://install.python-poetry.org | python3 -
ENV PATH="/root/.local/bin:${PATH}"

WORKDIR /root/caesar/pgcl/pgcl2heyvl/

# for discoverability, add the virtual environment in the project directory instead of
# somewhere in ~/.cache
RUN poetry config virtualenvs.in-project true

RUN poetry install --no-interaction

# ---- Entry point setup ----

# install common text editors for convenience
RUN apt-get install -y vim nano

WORKDIR /root/caesar
CMD ["/bin/bash", "/root/caesar/docker/hello.sh"]
