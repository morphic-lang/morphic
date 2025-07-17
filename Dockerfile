FROM ubuntu:24.04@sha256:b59d21599a2b151e23eea5f6602f4af4d7d31c4e236d22bf0b62b86d2e386b8f

ARG USERNAME=ubuntu

RUN apt-get update \
  && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    build-essential \
    cmake \
    ca-certificates \
    curl \
    git \
    gpg \
    gpg-agent \
    ssh \
    valgrind \
    vim \
    zlib1g-dev \
    libzstd-dev \
    libgmp3-dev \
    # Required for OCaml benchmarks
    opam \
    # Required for `summarize_results.py`
    python3-matplotlib \
    python3-seaborn \
    python3-numpy \
    python3-pandas

RUN gpg-agent --daemon \
  && curl -L https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add - \
  && echo "deb http://apt.llvm.org/noble/ llvm-toolchain-noble main" >> /etc/apt/sources.list \
  && echo "deb-src http://apt.llvm.org/noble/ llvm-toolchain-noble main" >> /etc/apt/sources.list \
  && apt-get update \
  && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    clang-16 \
    lld-16 \
    llvm-16-dev \
    llvm-16-tools \
    libpolly-16-dev \
  && apt-get clean \
  && rm -rf /var/lib/apt/lists/*

# Required for MLton benchmarks
RUN curl -LO https://github.com/MLton/mlton/releases/download/on-20241230-release/mlton-20241230-1.amd64-linux.ubuntu-24.04_static.tgz \
  && tar xzf mlton-20241230-1.amd64-linux.ubuntu-24.04_static.tgz \
  && rm mlton-20241230-1.amd64-linux.ubuntu-24.04_static.tgz \
  && mv mlton-20241230-1.amd64-linux.ubuntu-24.04_static /usr/local/mlton

ENV PATH="/usr/local/mlton/bin:${PATH}"

USER "ubuntu"

# Required for OCaml benchmarks
RUN opam init --bare --auto-setup --disable-sandboxing \
  && opam switch create 5.3.0 \
  && echo 'eval $(opam env)' >> /home/$USERNAME/.bashrc

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | bash -s -- -y

ENV PATH="/home/$USERNAME/.cargo/bin:${PATH}"

COPY --chown=$USERNAME:$USERNAME . /home/$USERNAME/morphic
WORKDIR /home/$USERNAME/morphic

RUN mkdir .cargo \
  # Use 'vendor-rust' to avoid overwriting our existing 'vendor' directory.
  && cargo vendor vendor-rust > .cargo/config.toml \
  && cargo test \
  # Increase stack size with a safety margin. Required for `bench_lisp.mor` with persistent arrays.
  && echo 'ulimit -s 262144' >> /home/$USERNAME/.bashrc
