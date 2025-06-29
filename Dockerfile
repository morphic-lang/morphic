FROM ubuntu:24.04@sha256:b59d21599a2b151e23eea5f6602f4af4d7d31c4e236d22bf0b62b86d2e386b8f

ARG USERNAME=ubuntu

RUN apt-get update \
  && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    build-essential \
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
    python3-matplotlib \
    python3-numpy

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

USER "ubuntu"

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | bash -s -- -y

ENV PATH="/home/$USERNAME/.cargo/bin:${PATH}"

COPY --chown=$USERNAME:$USERNAME . /home/$USERNAME/morphic
WORKDIR /home/$USERNAME/morphic

RUN cargo vendor \
  && cargo build \
  && cargo test
