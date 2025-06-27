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
    libzstd-dev
  #   sudo \
  #   # GHC for Haskell benchmarks
  #   ghc \
  #   ghc-prof \
  #   # Opam for OCaml benchmarks (see https://github.com/ocaml/opam/issues/5968#issuecomment-2151748424)
  #   opam \
  #   apparmor-profiles \
  # && ln -s /usr/share/apparmor/extra-profiles/bwrap-userns-restrict /etc/apparmor.d/

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

# RUN curl -LJo /tmp/mlton.tgz https://github.com/MLton/mlton/releases/download/on-20241230-release/mlton-20241230-1.amd64-linux.ubuntu-24.04_static.tgz \
#   && tar xf /tmp/mlton.tgz -C /tmp \
#   && cd /tmp/mlton-20241230-1.amd64-linux.ubuntu-24.04_static \
#   && make install

USER "ubuntu"

# RUN opam init --bare --auto-setup \
#   && opam switch create 5.3.0 \
#   && eval $(opam env)

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | bash -s -- -y

ENV PATH="/home/$USERNAME/.cargo/bin:${PATH}"

COPY --chown=$USERNAME:$USERNAME . /home/$USERNAME/morphic
WORKDIR /home/$USERNAME/morphic

RUN rm -rf .git \
  && cargo vendor \
  && cargo build \
  && cargo test
