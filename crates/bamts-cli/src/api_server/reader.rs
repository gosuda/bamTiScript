//! Frame reader and drop-enforced exit reporting.

use std::io::{self, BufRead};
use std::sync::Arc;

use super::control::{Admission, Control, ReaderExit};
use super::wire::{ApiError, Frame, MAX_FRAME_BYTES, Request, Response, read_frame};

pub(crate) struct ReaderExitGuard<'a> {
    control: &'a Control,
    exit: Option<ReaderExit>,
}

impl<'a> ReaderExitGuard<'a> {
    fn new(control: &'a Control) -> Self {
        Self {
            control,
            exit: Some(ReaderExit::Panicked),
        }
    }

    fn finish(&mut self, exit: ReaderExit) {
        self.exit = Some(exit);
    }
}

impl Drop for ReaderExitGuard<'_> {
    fn drop(&mut self) {
        self.control
            .reader_exited(self.exit.take().unwrap_or(ReaderExit::Panicked));
    }
}

pub(crate) fn reader_main<R: BufRead>(mut input: R, control: Arc<Control>) -> io::Result<()> {
    let mut guard = ReaderExitGuard::new(&control);
    loop {
        let frame = match read_frame(&mut input) {
            Ok(frame) => frame,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {
                guard.finish(ReaderExit::Woken);
                return Ok(());
            }
            Err(error) => {
                guard.finish(ReaderExit::Failed {
                    kind: error.kind(),
                    detail: error.to_string(),
                });
                return Err(error);
            }
        };
        match frame {
            Frame::Eof => {
                guard.finish(ReaderExit::Eof);
                return Ok(());
            }
            Frame::Payload(body) => {
                let admission = match serde_json::from_slice::<Request>(&body) {
                    Ok(request) => control.offer(request, body.len()),
                    Err(error) if error.is_data() => {
                        control.reject(None, ApiError::InvalidRequest(error.to_string()))
                    }
                    Err(error) => control.reject(None, ApiError::Parse(error.to_string())),
                };
                if matches!(admission, Admission::Halt) {
                    guard.finish(ReaderExit::Woken);
                    return Ok(());
                }
            }
            Frame::Oversize { declared } => {
                if matches!(
                    control.reject(
                        None,
                        ApiError::FrameTooLarge {
                            declared,
                            limit: MAX_FRAME_BYTES,
                        },
                    ),
                    Admission::Halt
                ) {
                    guard.finish(ReaderExit::Woken);
                    return Ok(());
                }
            }
            Frame::Malformed(detail) => {
                control.fatal(
                    Response::failure(None, ApiError::Parse(detail.clone())),
                    detail,
                );
                guard.finish(ReaderExit::Woken);
                return Ok(());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_frame_read_after_stop_still_earns_its_response() {
        let control = Control::new();
        control.stop();
        let request: Request =
            serde_json::from_str(r#"{"id":7,"method":"compiler/version"}"#).expect("request");
        assert!(matches!(control.offer(request, 32), Admission::Halt));
        assert_eq!(control.drain().len(), 1, "the drain answers it");

        let notification: Request =
            serde_json::from_str(r#"{"method":"compiler/version"}"#).expect("notification");
        assert!(matches!(control.offer(notification, 32), Admission::Halt));
        assert!(control.drain().is_empty(), "a notification owes no answer");
    }

    #[test]
    fn reader_guard_reports_panics() {
        let control = Arc::new(Control::new());
        let thread_control = Arc::clone(&control);
        let handle = std::thread::spawn(move || {
            let _guard = ReaderExitGuard::new(&thread_control);
            panic!("reader panic probe");
        });
        assert!(handle.join().is_err());
        assert!(control.wait_reaped(std::time::Duration::from_millis(100)));
        assert_eq!(control.next_reader_exit_for_test(), ReaderExit::Panicked);
    }
}
