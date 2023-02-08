#!/bin/bash

cargo clean
cargo build --release

bench() {
    for it in 0 1 2 3 4
    do
        for file in ~/ti-test-data/pizza-chili/*/*.${1}
        do
            ./target/release/ti-project --sais $1
        done
    done
}

bench 128MiB
