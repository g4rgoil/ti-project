#!/bin/bash

cargo clean
cargo build --release

bench() {
    for size in $1
    do
        for file in ~/ti-test-data/pizza-chili/*/*.${size}
        do
            ./target/release/ti-project --sais $file
        done
    done
}

bench "32MiB 64MiB 128MiB 256MiB 512MiB 1024MiB"
