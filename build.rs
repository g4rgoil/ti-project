fn main() {
    cc::Build::new()
        .file("libsais/src/libsais.c")
        .warnings_into_errors(true)
        .pic(true)
        .debug(false)
        .opt_level(2)
        .compile("libsais.a");
}
