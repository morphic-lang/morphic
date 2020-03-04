FROM debian:buster@sha256:c99ed5d068d4f7ff36c7a6f31810defebecca3a92267fefbe0e0cf2d9639115a

RUN apt-get update \
  && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    build-essential \
    ca-certificates \
    curl \
    git \
    gpg \
    gpg-agent \
    ssh \
    zlib1g-dev \
  && curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | bash -s -- -y

ENV PATH="/root/.cargo/bin:${PATH}"

RUN gpg-agent --daemon \
  && curl -L https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add - \
  && echo "deb http://apt.llvm.org/buster/ llvm-toolchain-buster-8 main" >> /etc/apt/sources.list \
  && echo "deb-src http://apt.llvm.org/buster/ llvm-toolchain-buster-8 main" >> /etc/apt/sources.list \
  && apt-get update \
  && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    clang-8 \
    llvm-8-dev \
  && apt-get clean \
  && rm -rf /var/lib/apt/lists/*
