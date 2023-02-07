#!/bin/bash

cargo clean
cargo build --features=no_lcp --release

bench() {
    for size in $3
    do
        echo "~/ti-test-data/pizza-chili/$1/$1.${size}"
        ./target/release/ti-project --sais ~/ti-test-data/pizza-chili/$1/$2.${size}
        ./target/release/ti-project --libsais ~/ti-test-data/pizza-chili/$1/$2.${size}
        ./target/release/ti-project --divsuf ~/ti-test-data/pizza-chili/$1/$2.${size}
    done
}

bench english english "32MiB 64MiB 128MiB 256MiB 512MiB 1024MiB"
bench dna dna "32MiB 64MiB 128MiB 256MiB"
bench proteins proteins "32MiB 64MiB 128MiB 256MiB 512MiB 1024MiB"
bench sources sources "32MiB 64MiB 128MiB"
bench xml dblp.xml "32MiB 64MiB 128MiB 256MiB"
