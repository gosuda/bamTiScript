//! Scratch directories for the service tests.

use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
    time::{SystemTime, UNIX_EPOCH},
};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

/// Creates a fresh, empty directory under the system temp directory.
///
/// The clock alone cannot make the name unique. macOS reads it in microseconds,
/// so tests that start together get the same value and collide on
/// `AlreadyExists`. The process-wide sequence number is what separates them,
/// and the process id and clock keep a directory left behind by an earlier run
/// from colliding with a new one.
pub(crate) fn fresh_dir(prefix: &str) -> PathBuf {
    let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "{prefix}-{}-{nonce}-{sequence}",
        std::process::id()
    ));
    fs::create_dir(&root).expect("create test directory");
    root
}

#[cfg(test)]
mod tests {
    use std::{
        collections::BTreeSet,
        sync::{Arc, Barrier},
        thread,
    };

    use super::fresh_dir;

    /// Threads that start together read the same clock value, so only the
    /// sequence number keeps their directories apart.
    #[test]
    fn directories_made_at_the_same_moment_are_distinct() {
        const THREADS: usize = 64;
        let start = Arc::new(Barrier::new(THREADS));
        let workers: Vec<_> = (0..THREADS)
            .map(|_| {
                let start = Arc::clone(&start);
                thread::spawn(move || {
                    start.wait();
                    fresh_dir("bamts-test-support")
                })
            })
            .collect();
        let roots: Vec<_> = workers
            .into_iter()
            .map(|worker| worker.join().expect("a directory is created without error"))
            .collect();

        let distinct: BTreeSet<_> = roots.iter().collect();
        assert_eq!(distinct.len(), THREADS);
        for root in &roots {
            assert!(root.is_dir(), "{} is not a directory", root.display());
            std::fs::remove_dir(root).expect("remove");
        }
    }
}
