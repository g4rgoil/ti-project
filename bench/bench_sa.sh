#!/bin/bash

cargo clean
cargo build --features=no_lcp --release


for file in ~/ti-test-data/pizza-chili/*/*.128MiB
do
    ./target/release/ti-project --sais $file
    ./target/release/ti-project --libsais $file
    ./target/release/ti-project --libdivsuf $file
done
