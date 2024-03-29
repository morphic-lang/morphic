FROM debian:buster@sha256:c99ed5d068d4f7ff36c7a6f31810defebecca3a92267fefbe0e0cf2d9639115a

ARG USERNAME
ARG UID
ARG GID

RUN if ! id -u "$USERNAME" >/dev/null 2>&1; then \
    addgroup --gid $GID "$USERNAME" \
    && adduser --disabled-password --gecos '' --uid $UID --gid $GID "$USERNAME" \
  ; fi

# We install GHC to run Haskell benchmarks. Building the compiler itself does not require GHC.
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
    ghc \
    ghc-prof

RUN gpg-agent --daemon \
  && curl -L https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add - \
  && echo "deb http://apt.llvm.org/buster/ llvm-toolchain-buster-14 main" >> /etc/apt/sources.list \
  && echo "deb-src http://apt.llvm.org/buster/ llvm-toolchain-buster-14 main" >> /etc/apt/sources.list \
  && apt-get update \
  && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    clang-14 \
    lld-14 \
    llvm-14-dev \
  && apt-get clean \
  && rm -rf /var/lib/apt/lists/* \
  && ln -s /usr/bin/wasm-ld-14 /usr/bin/wasm-ld

RUN curl -LJo /tmp/mlton.tgz https://github.com/MLton/mlton/releases/download/on-20201002-release/mlton-20201002-1.amd64-linux.tgz \
  && tar xf /tmp/mlton.tgz -C /tmp \
  && cd /tmp/mlton-20201002-1.amd64-linux \
  && make install

USER "$USERNAME"

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | bash -s -- -y

ENV PATH="${HOME}/.cargo/bin:${PATH}"
