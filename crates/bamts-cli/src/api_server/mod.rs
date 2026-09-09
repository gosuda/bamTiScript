//! Persistent bounded JSON-RPC transport for the compiler service.

mod control;
mod input;
mod reader;
mod session;
mod wire;

use std::io::{self, Write};
#[cfg(unix)]
use std::os::fd::AsFd;
use std::sync::Arc;
use std::thread;

use control::{Control, ControlKind, Inbound, Next, REAP_DEADLINE, ReaderExit};
use reader::reader_main;
use session::Session;

#[cfg(unix)]
pub use input::PollInput;
pub use input::{ChannelInput, ReaderWaker, SocketInput, TransportInput};
pub use wire::{ApiError, ErrorObject, Id, Request, Response};
use wire::{ApiError as TransportError, write_response};

use crate::cli::tsc_args::api_transport_requested;

#[derive(Debug)]
pub enum Reaped {
    Joined(io::Result<()>),
    Orphaned,
}

fn write_terminal<W: Write>(
    output: &mut W,
    response: &Response,
    first_error: &mut Option<io::Error>,
) {
    if first_error.is_none()
        && let Err(error) = write_response(output, response)
    {
        *first_error = Some(error);
    }
}

/// Serves one session and reports whether its reader was reaped. Inputs accepted
/// here carry their own safe wake capability; an opaque blocking `BufRead` is
/// intentionally not accepted.
#[doc(hidden)]
pub fn serve_reaped<I, W, E>(input: I, mut output: W, mut log: E) -> (io::Result<()>, Reaped)
where
    I: TransportInput,
    W: Write,
    E: Write,
{
    let (reader_half, waker) = match input.split() {
        Ok(parts) => parts,
        Err(error) => return (Err(error), Reaped::Joined(Ok(()))),
    };
    let control = Arc::new(Control::new());
    let reader_control = Arc::clone(&control);
    let reader = thread::spawn(move || reader_main(reader_half, reader_control));
    let mut session = Session::new();
    let mut first_error = None;
    let mut reader_failure = None;

    loop {
        match control.next() {
            Next::Inbound(Inbound::Work {
                ticket, request, ..
            }) => {
                let id = request.id.clone();
                let response = match control.begin(ticket, id.as_ref()) {
                    Err(()) => id
                        .clone()
                        .map(|id| Response::failure(Some(id), TransportError::Cancelled)),
                    Ok(token) => match session.plan(request, &token) {
                        Ok(planned) => session.apply(planned).or_else(|| {
                            id.clone().map(|id| {
                                Response::failure(
                                    Some(id),
                                    TransportError::Internal(
                                        "admitted request produced no response".to_owned(),
                                    ),
                                )
                            })
                        }),
                        Err(error) => id.clone().map(|id| Response::failure(Some(id), error)),
                    },
                };
                control.retire(ticket, id.as_ref());
                if let Some(response) = response {
                    write_terminal(&mut output, &response, &mut first_error);
                    if first_error.is_some() {
                        control.stop();
                        let _ = waker.wake();
                        break;
                    }
                }
                if session.stopped() {
                    control.stop();
                    let _ = waker.wake();
                    break;
                }
            }
            Next::Inbound(Inbound::Reject { ticket, id, error }) => {
                let response = Response::failure(id.clone(), error);
                control.retire(ticket, id.as_ref());
                write_terminal(&mut output, &response, &mut first_error);
                if first_error.is_some() {
                    control.stop();
                    let _ = waker.wake();
                    break;
                }
            }
            Next::Inbound(Inbound::Control(kind)) => match kind {
                ControlKind::Shutdown => {}
                ControlKind::Exit => {
                    control.stop();
                    let _ = waker.wake();
                    break;
                }
            },
            Next::Fatal(response, detail) => {
                write_terminal(&mut output, &response, &mut first_error);
                if first_error.is_none()
                    && let Err(error) = writeln!(
                        log,
                        "api: closing after an unrecoverable transport error: {detail}"
                    )
                {
                    first_error = Some(error);
                }
                control.stop();
                let _ = waker.wake();
                break;
            }
            Next::ReaderExited(exit) => {
                if let ReaderExit::Failed { kind, detail } = exit {
                    reader_failure = Some(io::Error::new(kind, detail));
                }
                break;
            }
        }
    }

    control.stop();
    let _ = waker.wake();
    // `shutdown` ends the loop by design, and the drain owes a terminal
    // response to work the transport already carried. Reaping the reader
    // first is what makes that set well defined: without it the loop can
    // break while the next frame is still being parsed, and that request
    // leaves unanswered depending only on thread scheduling. One wait
    // serves both the drain and the join below, so a reader that never
    // exits costs the deadline once. A reader that cannot be woken keeps
    // the existing orphan path rather than stalling shutdown at all.
    let reader_reaped = I::Waker::REAPABLE && control.wait_reaped(REAP_DEADLINE);
    for inbound in control.drain() {
        match inbound {
            Inbound::Work {
                ticket, request, ..
            } => {
                let id = request.id.clone();
                control.retire(ticket, id.as_ref());
                if let Some(id) = id {
                    write_terminal(
                        &mut output,
                        &Response::failure(Some(id), TransportError::Cancelled),
                        &mut first_error,
                    );
                }
            }
            Inbound::Reject { ticket, id, error } => {
                control.retire(ticket, id.as_ref());
                write_terminal(&mut output, &Response::failure(id, error), &mut first_error);
            }
            Inbound::Control(_) => {}
        }
    }

    let reaped = if reader_reaped {
        Reaped::Joined(
            reader
                .join()
                .map_err(|_| io::Error::other("api reader thread panicked"))
                .and_then(|result| result),
        )
    } else {
        drop(reader);
        Reaped::Orphaned
    };

    let result = first_error
        .map_or_else(|| reader_failure.map_or(Ok(()), Err), Err)
        .and_then(|()| match &reaped {
            Reaped::Joined(Err(error)) => Err(io::Error::new(error.kind(), error.to_string())),
            Reaped::Joined(Ok(())) | Reaped::Orphaned => Ok(()),
        });
    (result, reaped)
}

pub fn serve<I, W, E>(input: I, output: W, log: E) -> io::Result<()>
where
    I: TransportInput,
    W: Write,
    E: Write,
{
    serve_reaped(input, output, log).0
}

/// Runs the transport when argv selects it, keeping stdout protocol-only.
#[must_use]
pub fn maybe_run(argv: &[String]) -> Option<i32> {
    if !api_transport_requested(argv) {
        return None;
    }

    // fd0 may be a socket (Node `stdio: "pipe"`), which no pathname can reopen;
    // duplicating the inherited descriptor preserves it. `io::stdin()` itself is
    // buffered, so it cannot feed the poll-driven reader directly.
    #[cfg(unix)]
    let result = io::stdin()
        .as_fd()
        .try_clone_to_owned()
        .map(std::fs::File::from)
        .and_then(|stdin| serve(PollInput(stdin), io::stdout().lock(), io::stderr().lock()));
    #[cfg(windows)]
    let result = serve(
        input::BlockingStdin,
        io::stdout().lock(),
        io::stderr().lock(),
    );

    Some(match result {
        Ok(()) => 0,
        Err(error) => {
            let _ = writeln!(io::stderr().lock(), "api: transport failed: {error}");
            1
        }
    })
}

#[cfg(test)]
mod tests;
