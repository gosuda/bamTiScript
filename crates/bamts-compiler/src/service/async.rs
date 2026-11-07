use std::{
    num::NonZeroUsize,
    path::Path,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

use crate::source::Utf16Pos;

use super::{
    Completion, DiagnosticEntry, DocumentSnapshot, Location, QuickInfo, RenameResult, ServiceError,
    ServiceSnapshot, filesystem::FileSystem, sync::SyncService,
};

pub use bamts_cancel::CancellationToken;

/// Async facade over the exact synchronous implementation. It contributes only
/// cancellation and a bounded in-flight request count.
pub struct AsyncService<F: FileSystem> {
    sync: SyncService<F>,
    limiter: Arc<RequestLimiter>,
}

impl<F: FileSystem> Clone for AsyncService<F> {
    fn clone(&self) -> Self {
        Self {
            sync: self.sync.clone(),
            limiter: Arc::clone(&self.limiter),
        }
    }
}

impl<F: FileSystem> AsyncService<F> {
    #[must_use]
    pub fn new(filesystem: F, max_in_flight: NonZeroUsize) -> Self {
        Self {
            sync: SyncService::new(filesystem),
            limiter: Arc::new(RequestLimiter::new(max_in_flight.get())),
        }
    }

    #[must_use]
    pub fn from_sync(sync: SyncService<F>, max_in_flight: NonZeroUsize) -> Self {
        Self {
            sync,
            limiter: Arc::new(RequestLimiter::new(max_in_flight.get())),
        }
    }

    #[must_use]
    pub fn synchronous(&self) -> SyncService<F> {
        self.sync.clone()
    }

    pub async fn open(
        &self,
        path: impl AsRef<Path>,
        text: impl Into<Arc<str>>,
        version: u64,
        cancellation: &CancellationToken,
    ) -> Result<Arc<DocumentSnapshot>, ServiceError> {
        let _permit = self.begin(cancellation)?;
        self.sync
            .open_with_cancel(path, text, version, cancellation.clone())
    }

    pub async fn update(
        &self,
        path: impl AsRef<Path>,
        text: impl Into<Arc<str>>,
        version: u64,
        cancellation: &CancellationToken,
    ) -> Result<Arc<DocumentSnapshot>, ServiceError> {
        let _permit = self.begin(cancellation)?;
        self.sync
            .update_with_cancel(path, text, version, cancellation.clone())
    }

    pub async fn close(
        &self,
        path: impl AsRef<Path>,
        cancellation: &CancellationToken,
    ) -> Result<(), ServiceError> {
        let _permit = self.begin(cancellation)?;
        self.sync.close_with_cancel(path, cancellation.clone())
    }

    pub async fn snapshot(
        &self,
        cancellation: &CancellationToken,
    ) -> Result<ServiceSnapshot, ServiceError> {
        let _permit = self.begin(cancellation)?;
        self.sync.snapshot()
    }

    pub async fn completions(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
        cancellation: &CancellationToken,
    ) -> Result<Vec<Completion>, ServiceError> {
        let _permit = self.begin(cancellation)?;
        self.sync
            .completions_with_cancel(path, position, cancellation.clone())
    }

    pub async fn definition(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
        cancellation: &CancellationToken,
    ) -> Result<Option<Location>, ServiceError> {
        let _permit = self.begin(cancellation)?;
        self.sync
            .definition_with_cancel(path, position, cancellation.clone())
    }

    pub async fn quick_info(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
        cancellation: &CancellationToken,
    ) -> Result<Option<QuickInfo>, ServiceError> {
        let _permit = self.begin(cancellation)?;
        self.sync
            .quick_info_with_cancel(path, position, cancellation.clone())
    }

    pub async fn references(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
        cancellation: &CancellationToken,
    ) -> Result<Vec<Location>, ServiceError> {
        let _permit = self.begin(cancellation)?;
        self.sync
            .references_with_cancel(path, position, cancellation.clone())
    }

    pub async fn rename(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
        new_name: &str,
        cancellation: &CancellationToken,
    ) -> Result<RenameResult, ServiceError> {
        let _permit = self.begin(cancellation)?;
        self.sync
            .rename_with_cancel(path, position, new_name, cancellation.clone())
    }

    pub async fn diagnostics(
        &self,
        path: impl AsRef<Path>,
        cancellation: &CancellationToken,
    ) -> Result<Vec<DiagnosticEntry>, ServiceError> {
        let _permit = self.begin(cancellation)?;
        self.sync
            .diagnostics_with_cancel(path, cancellation.clone())
    }

    fn begin<'a>(
        &'a self,
        cancellation: &CancellationToken,
    ) -> Result<RequestPermit<'a>, ServiceError> {
        cancellation.check().map_err(|_| ServiceError::Cancelled)?;
        let permit = self
            .limiter
            .try_acquire()
            .ok_or(ServiceError::Backpressure)?;
        if cancellation.check().is_err() {
            return Err(ServiceError::Cancelled);
        }
        Ok(permit)
    }
}

#[derive(Debug)]
struct RequestLimiter {
    active: AtomicUsize,
    maximum: usize,
}

impl RequestLimiter {
    const fn new(maximum: usize) -> Self {
        Self {
            active: AtomicUsize::new(0),
            maximum,
        }
    }

    fn try_acquire(&self) -> Option<RequestPermit<'_>> {
        let mut active = self.active.load(Ordering::Acquire);
        loop {
            if active >= self.maximum {
                return None;
            }
            match self.active.compare_exchange_weak(
                active,
                active + 1,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return Some(RequestPermit { limiter: self }),
                Err(observed) => active = observed,
            }
        }
    }
}

struct RequestPermit<'a> {
    limiter: &'a RequestLimiter,
}

impl Drop for RequestPermit<'_> {
    fn drop(&mut self) {
        self.limiter.active.fetch_sub(1, Ordering::AcqRel);
    }
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        future::Future,
        num::NonZeroUsize,
        sync::Arc,
        task::{Context, Poll, Waker},
    };

    use super::{AsyncService, CancellationToken};
    use crate::{
        service::{ServiceError, filesystem::OsFileSystem},
        source::Utf16Pos,
    };

    fn ready<T>(future: impl Future<Output = T>) -> T {
        let mut future = Box::pin(future);
        let waker = Waker::noop();
        match future.as_mut().poll(&mut Context::from_waker(waker)) {
            Poll::Ready(output) => output,
            Poll::Pending => panic!("service future unexpectedly pending"),
        }
    }

    fn service() -> (std::path::PathBuf, AsyncService<OsFileSystem>) {
        let root = crate::service::test_support::fresh_dir("bamts-async-service");
        let service = AsyncService::new(
            OsFileSystem::new(&root).expect("filesystem"),
            NonZeroUsize::new(1).expect("nonzero"),
        );
        (root, service)
    }

    #[test]
    fn async_delegates_to_sync_and_honors_cancellation() {
        let (root, service) = service();
        let active = CancellationToken::new();
        ready(service.open("a.ts", Arc::<str>::from("const a = 1;"), 1, &active)).expect("open");
        assert_eq!(
            service
                .synchronous()
                .snapshot()
                .expect("sync snapshot")
                .documents()
                .count(),
            1
        );

        let cancelled = CancellationToken::new();
        cancelled.cancel();
        assert!(matches!(
            ready(service.snapshot(&cancelled)),
            Err(ServiceError::Cancelled)
        ));
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn async_rejects_work_when_capacity_is_exhausted() {
        let (root, service) = service();
        let _held = service.limiter.try_acquire().expect("hold sole permit");
        assert!(matches!(
            ready(service.snapshot(&CancellationToken::new())),
            Err(ServiceError::Backpressure)
        ));
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn async_and_sync_queries_have_identical_results() {
        let (root, service) = service();
        let token = CancellationToken::new();
        let source = "const answer = 1;\nans\nanswer;\n";
        ready(service.open("a.ts", source, 1, &token)).expect("async open");

        let sync = service.synchronous();
        assert_eq!(
            ready(service.completions("a.ts", Utf16Pos::new(21), &token))
                .expect("async completions"),
            sync.completions("a.ts", Utf16Pos::new(21))
                .expect("sync completions")
        );
        assert_eq!(
            ready(service.definition("a.ts", Utf16Pos::new(28), &token)).expect("async definition"),
            sync.definition("a.ts", Utf16Pos::new(28))
                .expect("sync definition")
        );
        assert_eq!(
            ready(service.references("a.ts", Utf16Pos::new(28), &token)).expect("async references"),
            sync.references("a.ts", Utf16Pos::new(28))
                .expect("sync references")
        );
        assert_eq!(
            ready(service.rename("a.ts", Utf16Pos::new(28), "result", &token))
                .expect("async rename"),
            sync.rename("a.ts", Utf16Pos::new(28), "result")
                .expect("sync rename")
        );
        assert_eq!(
            ready(service.diagnostics("a.ts", &token)).expect("async diagnostics"),
            sync.diagnostics("a.ts").expect("sync diagnostics")
        );

        let async_snapshot = ready(service.snapshot(&token)).expect("async snapshot");
        let sync_snapshot = sync.snapshot().expect("sync snapshot");
        let project_view = |snapshot: &crate::service::ServiceSnapshot| {
            snapshot
                .documents()
                .map(|document| {
                    (
                        document.path().to_path_buf(),
                        document.version(),
                        document.is_open(),
                    )
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(project_view(&async_snapshot), project_view(&sync_snapshot));

        ready(service.update("a.ts", "const answer = 2;", 2, &token)).expect("async update");
        assert_eq!(
            sync.snapshot()
                .expect("updated snapshot")
                .document(&root.join("a.ts"))
                .expect("updated document")
                .version(),
            2
        );
        ready(service.close("a.ts", &token)).expect("async close");
        assert!(
            sync.snapshot()
                .expect("closed snapshot")
                .document(&root.join("a.ts"))
                .is_none()
        );
        fs::remove_dir_all(root).expect("remove root");
    }
}
