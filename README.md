# Text-Indexierung Project

Project for the lecture [Text-Indexierung](https://algo2.iti.kit.edu/4326.php) during winter term 2022/23.

- Implements suffix array construction using Suffix Array Induced Sorting (SAIS).
  A naive algorithm is also implemented as reference.
- Implements LCP array construction using the naive algorithm, the algorithm presented by Kasai et al., and the Phi array algorithm.

# Setup

Building the project requires an up-to-date version of Rust (tested with 1.66.0).
On Ubuntu 20.04 this requires installing through [`rustup`](https://rustup.rs) rather than `apt`.

```sh
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

No further external dependencies are required to build and run the project.

# Build

The project can be built using Cargo.

```sh
cargo build --release
```

# Running

To measure running times and memory usage for suffix and LCP array construction for a text, simply run 

```sh
./target/release/ti-project <file>
```


