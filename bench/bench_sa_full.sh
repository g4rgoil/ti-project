#!/bin/bash

cargo clean
cargo build --features=no_lcp --release

bench() {
    echo "~/ti-test-data/pizza-chili/$1/$1.${size}"
    ./target/release/ti-project --sais ~/ti-test-data/pizza-chili/$1
    ./target/release/ti-project --libsais ~/ti-test-data/pizza-chili/$1
    ./target/release/ti-project --divsuf ~/ti-test-data/pizza-chili/$1
}

bench english/english
bench dna/dna
bench proteins/proteins
bench sources/sources
bench xml/dblp.xml
bench pitches/pitches
