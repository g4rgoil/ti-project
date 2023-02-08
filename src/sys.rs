#[rustfmt::skip]
extern "C" {
    pub fn libsais(
        T: *const u8,
        SA: *mut i32,
        n: i32,
        fs: i32,
        freq: *const i32,
    ) -> i32;
}

#[rustfmt::skip]
extern "C" {
    pub fn libsais64(
        T: *const u8,
        SA: *mut i64,
        n: i64,
        fs: i64, 
        freq: *const i64
    ) -> i64;
}
