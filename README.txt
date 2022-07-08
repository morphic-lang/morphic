Morphic's only system dependencies are a Rust environment and the LLVM-10
development libraries. An appropriate Rust environment can be installed by
running "curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh" (see
<https://rustup.rs>).

A Dockerfile with these dependencies is provided in the "docker" folder.
Scripts "docker/build_linux" and "docker/build_macos" invoke the docker
executable with the appropriate arguements to build an image with tag "morphic"
from this Dockerfile. We highly recommend utilizing the Dockerfile.

In the Morphic directory, on your system or inside your Docker container:
- "cargo build" will build Morphic
- "cargo test" will run Morphic's test suite
- "cargo run -- <args>" will run Morphic with arguments <args>

Sample Morphic programs can be found in the "samples" directory. For further
help, try invoking Morphic's help command: "cargo run -- help".
