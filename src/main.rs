// TODO use stricter clippy options
// TODO remove
#![allow(clippy::missing_safety_doc)]
#![allow(unused)]


// TODO define prelude

pub mod lcp_array;
pub mod num;
pub mod sais;
pub mod suffix_array;
pub mod text;

use std::process::{self, ExitCode};
use std::time::{Duration, Instant};
use std::{env, fs, hint, io};

use lcp_array as lcp;
use num::ArrayIndex;
use suffix_array as sa;

use crate::sa::SuffixArray;
use crate::sais::index::SignedIndex;
use crate::text::Text;

pub fn main() -> Result<TestResults, String> {
    #[inline(never)]
    fn run_timed<T>(f: impl FnOnce() -> T) -> (T, Duration) {
        let before = Instant::now();
        let result = hint::black_box(f());
        let elapsed = before.elapsed();
        (result, elapsed)
    }

    fn run(text: &Text<u8>) -> Result<TestResults, String> {
        None.or_else(|| try_run_sa::<u32>(text))
            .or_else(|| try_run_sa::<u64>(text))
            .or_else(|| try_run_sa::<usize>(text))
            .ok_or_else(|| {
                format!("cannot find index size for text of length {}", text.len())
            })
    }

    fn try_run_sa<Idx: sais::index::Index>(text: &Text<u8>) -> Option<TestResults>
    where
        Idx::Signed: SignedIndex,
    {
        let (result, sa_time) = run_timed(|| sa::sais::<Idx>(text));

        // let times: Box<[Duration]> = std::iter::once(sa_time)
        //     .chain((0..5).map(|_| run_timed(|| sa::sais::<Idx>(text)).1))
        //     .map(|duration| dbg!(duration))
        //     .collect();
        //
        // println!(
        //     "min={:?}, max={:?}, avg={:?}",
        //     times.iter().min().unwrap(),
        //     times.iter().max().unwrap(),
        //     times.iter().sum::<Duration>() / times.len() as u32
        // );

        if let Ok((sa_memory, sa)) = result {
            #[cfg(feature = "verify")]
            {
                println!("verifying SA");
                sa.verify(text);
            }

            Some(TestResults { sa_time, sa_memory, ..run_lcp(text, sa) })
        } else {
            None
        }
    }

    fn run_lcp<Idx: ArrayIndex>(
        text: &Text<u8>,
        sa: SuffixArray<u8, Idx>,
    ) -> TestResults {
        // let (_lcp_naive, lcp_naive_time) = run_timed(|| lcp::naive(&sa));
        // let (_lcp_kasai, lcp_kasai_time) = run_timed(|| lcp::kasai(&sa.inverse()));
        // let (_lcp_phi, lcp_phi_time) = run_timed(|| lcp::phi(&sa));
        //
        // #[cfg(feature = "verify")]
        // {
        //     _lcp_naive.verify();
        //     _lcp_kasai.verify();
        //     _lcp_phi.verify();
        // }
        //
        // TestResults { lcp_naive_time, lcp_kasai_time, lcp_phi_time, ..Default::default() }
        Default::default()
    }

    let param = env::args().nth(1);
    let input_path = param.ok_or_else(|| "expected exactly 1 argument".to_owned())?;
    let input_file = fs::read(input_path).map_err(|e| e.to_string())?;
    run(Text::from_slice(&input_file))
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
