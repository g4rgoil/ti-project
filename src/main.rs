mod lcp_array;
mod suffix_array;

use std::{
    env, fs, io,
    process::{self, ExitCode},
    time::{Duration, Instant},
};

use lcp_array as lcp;
use suffix_array as sa;

fn main() -> Result<TestResults, String> {
    // TODO Error enum

    fn run_timed<T>(f: impl FnOnce() -> T) -> (T, Duration) {
        let before = Instant::now();
        let result = f();
        let elapsed = before.elapsed();
        (result, elapsed)
    }

    let input_path =
        env::args().nth(1).ok_or("expected exactly 1 argument".to_owned())?;
    let input_file = fs::read(input_path).map_err(|e| e.to_string())?;

    let (sa, sa_time) = run_timed(|| sa::naive(&input_file));
    // TODO sa memory

    let (_, lcp_naive_time) = run_timed(|| lcp::naive(&input_file, &sa));

    Ok(TestResults {
        sa_time,
        sa_memory: Default::default(),
        lcp_naive_time,
        lcp_kasai_time: Default::default(),
        lcp_phi_time: Default::default(),
    })
}

#[derive(Debug, Clone, Copy, Default)]
pub struct TestResults {
    sa_time: Duration,
    sa_memory: u64,
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
            self.sa_memory,
            self.lcp_naive_time.as_millis(),
            self.lcp_kasai_time.as_millis(),
            self.lcp_phi_time.as_millis()
        );
        ExitCode::SUCCESS
    }
}

pub trait TextExt<T: Ord> {
    fn suffix(&self, i: usize) -> &Self;
}

impl<T: Ord> TextExt<T> for [T] {
    fn suffix(&self, i: usize) -> &Self {
        &self[i..]
    }
}
