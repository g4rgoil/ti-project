// TODO use stricter clippy options

pub mod index;
pub mod lcp_array;
pub mod suffix_array;
pub mod text;

use std::process::{self, ExitCode};
use std::time::{Duration, Instant};
use std::{env, fs, io};

use index::ArrayIndex;
use lcp_array as lcp;
use suffix_array as sa;

use crate::suffix_array::result::MemoryResult;
use crate::text::Text;

pub fn main() -> Result<TestResults, String> {
    #[inline(never)]
    fn run_timed<T>(f: impl FnOnce() -> T) -> (T, Duration) {
        let before = Instant::now();
        let result = f();
        let elapsed = before.elapsed();
        (result, elapsed)
    }

    fn run<Idx: ArrayIndex>(text: &Text<u8>) -> TestResults {
        let (result, sa_time) = run_timed(|| sa::sais::<Idx>(text));
        let MemoryResult { value: sa, memory: sa_memory } = result;

        #[cfg(feature = "verify")]
        sa.verify(text);

        let (_lcp_naive, lcp_naive_time) = run_timed(|| lcp::naive(&sa));
        let (_lcp_kasai, lcp_kasai_time) = run_timed(|| lcp::kasai(&sa.inverse()));
        let (_lcp_phi, lcp_phi_time) = run_timed(|| lcp::phi(&sa));

        #[cfg(feature = "verify")]
        {
            _lcp_naive.verify();
            _lcp_kasai.verify();
            _lcp_phi.verify();
        }
        // assert_eq!(lcp_naive.inner(), lcp_kasai.inner());
        // assert_eq!(lcp_kasai.inner(), lcp_phi.inner());

        TestResults { sa_time, sa_memory, lcp_naive_time, lcp_kasai_time, lcp_phi_time }
    }

    let input_path =
        env::args().nth(1).ok_or_else(|| "expected exactly 1 argument".to_owned())?;
    let input_file = fs::read(input_path).map_err(|e| e.to_string())?;
    let text = Text::from_slice(&input_file);

    match () {
        _ if text.fits_index::<u16>() => Ok(run::<u16>(text)),

        #[cfg(any(target_pointer_width = "64", target_pointer_width = "32"))]
        _ if text.fits_index::<u32>() => Ok(run::<u32>(text)),

        #[cfg(target_pointer_width = "64")]
        _ if text.fits_index::<u64>() => Ok(run::<u64>(text)),

        _ => Ok(run::<usize>(text)),
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
