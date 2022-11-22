use std::{
    io,
    process::{self, ExitCode},
};

fn main() -> Result<TestResults, String> {
    Ok(Default::default())
}

#[derive(Debug, Clone, Copy, Default)]
pub struct TestResults {
    sa_time: u64,
    sa_memory: u64,
    lcp_naive_time: u64,
    lcp_kasai_time: u64,
    lcp_phi_time: u64,
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
            self.sa_time,
            self.sa_memory,
            self.lcp_naive_time,
            self.lcp_kasai_time,
            self.lcp_phi_time
        );
        ExitCode::SUCCESS
    }
}
