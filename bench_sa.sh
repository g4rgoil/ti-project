#!/bin/bash

cargo clean
cargo build --features=no_lcp --release

bench() {
    for size in $2
    do
        echo "~/ti-test-data/pizza-chili/$1/$1.${size}"
        ./target/release/ti-project --sais ~/ti-test-data/pizza-chili/$1/$1.${size}
        ./target/release/ti-project --libsais ~/ti-test-data/pizza-chili/$1/$1.${size}
        ./target/release/ti-project --divsuf ~/ti-test-data/pizza-chili/$1/$1.${size}
    done
}

bench english "64MiB 128MiB 256MiB 512MiB 1024MiB"
