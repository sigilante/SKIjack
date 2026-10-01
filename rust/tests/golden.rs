//! Conformance against the reference implementation's CLI.
//!
//! ``tests/golden.manifest`` holds, for every invocation the reference
//! CLI was run with over the corpus (every flag, every liftable name,
//! every level-1 declaration), the sha256 of its stdout, exit code and
//! stderr.  This test runs the same invocations through the Rust binary
//! from the same working directory and compares digests.  Regenerate the
//! manifest with ``bench/golden.sh`` after a deliberate output change.

use std::path::PathBuf;
use std::process::Command;
use std::sync::{Arc, Mutex};

use sha2::{Digest, Sha256};

fn python_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..").join("python")
}

#[test]
fn every_reference_invocation_matches() {
    let manifest = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/golden.manifest")).unwrap();
    let lines: Vec<(String, Vec<String>)> = manifest
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .map(|l| {
            let (h, rest) = l.split_once(' ').unwrap();
            (h.to_string(), rest.split(' ').map(|s| s.to_string()).collect())
        })
        .collect();
    assert!(lines.len() > 2000, "manifest looks truncated: {} lines", lines.len());
    let bin = env!("CARGO_BIN_EXE_skijack");
    let cwd = python_dir();
    let failures = Arc::new(Mutex::new(Vec::new()));
    let jobs = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4).min(32);
    let chunks: Vec<Vec<(String, Vec<String>)>> = (0..jobs).map(|j| lines.iter().skip(j).step_by(jobs).cloned().collect()).collect();
    let handles: Vec<_> = chunks
        .into_iter()
        .map(|chunk| {
            let failures = failures.clone();
            let cwd = cwd.clone();
            std::thread::spawn(move || {
                for (want, args) in chunk {
                    let out = Command::new(bin).args(&args).current_dir(&cwd).output().expect("run skijack");
                    let mut h = Sha256::new();
                    h.update(&out.stdout);
                    h.update(format!("--- exit {}\n", out.status.code().unwrap_or(-1)).as_bytes());
                    h.update(&out.stderr);
                    let got: String = h.finalize().iter().map(|b| format!("{:02x}", b)).collect();
                    if got != want {
                        failures.lock().unwrap().push(format!("skijack {}", args.join(" ")));
                    }
                }
            })
        })
        .collect();
    for h in handles {
        h.join().unwrap();
    }
    let failures = failures.lock().unwrap();
    assert!(
        failures.is_empty(),
        "{} invocation(s) differ from the reference CLI (run from python/):\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
