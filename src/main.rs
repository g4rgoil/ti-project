// TODO use stricter clippy options

mod index;
mod lcp_array;
mod suffix_array;

use std::{
    env, fs, io,
    process::{self, ExitCode},
    time::{Duration, Instant},
};

use index::ArrayIndex;
use lcp_array as lcp;
use suffix_array as sa;

use crate::suffix_array::result::MemoryResult;

fn main() -> Result<TestResults, String> {
    fn run_timed<T>(f: impl FnOnce() -> T) -> (T, Duration) {
        let before = Instant::now();
        let result = f();
        let elapsed = before.elapsed();
        (result, elapsed)
    }

    fn run<Idx: ArrayIndex>(input: &[u8]) -> TestResults {
        let (result, sa_time) = run_timed(|| sa::sais::<Idx>(input));
        let MemoryResult { value: sa, memory: sa_memory } = result;

        let (lcp_naive, lcp_naive_time) = run_timed(|| lcp::naive(input, &sa));
        let (lcp_kasai, lcp_kasai_time) = run_timed(|| {
            let isa = sa.inverse();
            lcp::kasai(input, &sa, &isa)
        });
        let (lcp_phi, lcp_phi_time) = run_timed(|| lcp::phi(input, &sa));

        assert_eq!(*lcp_naive, *lcp_kasai);
        assert_eq!(*lcp_kasai, *lcp_phi);

        TestResults {
            sa_time,
            sa_memory,
            lcp_naive_time,
            lcp_kasai_time,
            lcp_phi_time,
        }
    }

    let input_path = env::args()
        .nth(1)
        .ok_or_else(|| "expected exactly 1 argument".to_owned())?;
    let input_file = fs::read(input_path).map_err(|e| e.to_string())?;

    // todo add cfg[target_width ] options
    if input_file.fits::<u16>() {
        // TODO this is pretty much useless
        Ok(run::<u16>(&input_file))
    } else if input_file.fits::<u32>() {
        Ok(run::<u32>(&input_file))
    } else if input_file.fits::<u64>() {
        Ok(run::<u64>(&input_file))
    } else {
        Ok(run::<usize>(&input_file))
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct TestResults {
    sa_time: Duration,
    sa_memory: usize,
    lcp_naive_time: Duration,
    lcp_kasai_time: Duration,
    lcp_phi_time: Duration,
}

impl process::Termination for TestResults {
    fn report(self) -> process::ExitCode {
        use io::Write;

        let _ = writeln!(
            io::stderr(),
            "RESULT name=Pascal\tMehnert \
            sa_construction_time={} \
            sa_construction_memory={} \
            lcp_naive_construction_time={} \
            lcp_kasai_construction_time={} \
            lcp_phi_construction_time={}",
            self.sa_time.as_millis(),
            self.sa_memory / (1024 * 1024),
            self.lcp_naive_time.as_millis(),
            self.lcp_kasai_time.as_millis(),
            self.lcp_phi_time.as_millis()
        );
        ExitCode::SUCCESS
    }
}

// TODO free function instead of Trait? together with common_prefix?
pub trait TextExt<T: Ord> {
    fn suffix(&self, i: usize) -> &Self;

    fn fits<Idx: ArrayIndex>(&self) -> bool;
}

impl<T: Ord> TextExt<T> for [T] {
    fn suffix(&self, i: usize) -> &Self { &self[i..] }

    fn fits<Idx: ArrayIndex>(&self) -> bool { self.len() <= Idx::MAX.as_() }
}
