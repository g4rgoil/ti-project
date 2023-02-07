extern "C" {
    pub fn libsais(
        T: *const u8,
        SA: *mut i32,
        n: i32,
        fs: i32,
        freq: *const i32,
    ) -> i32;
}
