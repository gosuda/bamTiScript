//! Total bounded admission and cancellation ownership.

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Condvar, Mutex};
use std::time::{Duration, Instant};

use bamts_compiler::service::r#async::CancellationToken;

use super::wire::{ApiError, Id, Request, Response};

pub(crate) const MAX_ID_BYTES: usize = 512;
pub(crate) const MAX_QUEUED_WORK: usize = 64;
pub(crate) const MAX_QUEUED_BYTES: usize = 8 * 1024 * 1024;
pub(crate) const MAX_QUEUED_REJECTS: usize = 1024;
pub(crate) const REAP_DEADLINE: Duration = Duration::from_secs(5);

pub(crate) type Ticket = u64;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ControlKind {
    Shutdown,
    Exit,
}

#[derive(Debug)]
pub(crate) enum Inbound {
    Work {
        ticket: Ticket,
        request: Request,
        bytes: usize,
    },
    Reject {
        ticket: Ticket,
        id: Option<Id>,
        error: ApiError,
    },
    Control(ControlKind),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ReaderExit {
    Eof,
    Woken,
    Failed {
        kind: std::io::ErrorKind,
        detail: String,
    },
    Panicked,
}

pub(crate) enum Admission {
    Accepted,
    Halt,
}

pub(crate) enum Next {
    Inbound(Inbound),
    Fatal(Response, String),
    ReaderExited(ReaderExit),
}

struct Inner {
    queue: VecDeque<Inbound>,
    queued_work: usize,
    queued_bytes: usize,
    queued_rejects: usize,
    outstanding: HashMap<Id, Ticket>,
    precancelled: HashSet<Ticket>,
    executing: Option<(Ticket, Option<Id>, CancellationToken)>,
    next_ticket: Ticket,
    stop: bool,
    reader_exit: Option<ReaderExit>,
    fatal: Option<(Response, String)>,
}

pub(crate) struct Control {
    inner: Mutex<Inner>,
    ready: Condvar,
    reaped: Condvar,
}

impl Control {
    pub(crate) fn new() -> Self {
        Self {
            inner: Mutex::new(Inner {
                queue: VecDeque::new(),
                queued_work: 0,
                queued_bytes: 0,
                queued_rejects: 0,
                outstanding: HashMap::new(),
                precancelled: HashSet::new(),
                executing: None,
                next_ticket: 1,
                stop: false,
                reader_exit: None,
                fatal: None,
            }),
            ready: Condvar::new(),
            reaped: Condvar::new(),
        }
    }

    pub(crate) fn offer(&self, request: Request, bytes: usize) -> Admission {
        let mut inner = self.inner.lock().expect("transport control poisoned");
        if inner.fatal.is_some() {
            return Admission::Halt;
        }
        // A frame already read still earns its terminal response: the drain runs
        // after the reader exits, so the request only has to reach the queue.
        let stopping = inner.stop;
        if stopping && request.id.is_none() {
            return Admission::Halt;
        }
        let admission = self.admit_locked(&mut inner, request, bytes);
        if stopping { Admission::Halt } else { admission }
    }

    fn admit_locked(&self, inner: &mut Inner, request: Request, bytes: usize) -> Admission {
        if request.id.is_none() {
            match request.method.as_str() {
                "$/cancelRequest" => {
                    if let Some(id) = cancellation_id(&request) {
                        cancel_locked(inner, &id);
                    }
                    self.ready.notify_one();
                    return Admission::Accepted;
                }
                "shutdown" => {
                    inner.queue_control(ControlKind::Shutdown);
                    self.ready.notify_one();
                    return Admission::Accepted;
                }
                "exit" => {
                    inner.queue_control(ControlKind::Exit);
                    self.ready.notify_one();
                    return Admission::Halt;
                }
                _ => {}
            }
        }

        let ticket = inner.allocate_ticket();
        let id = request.id.clone();

        if let Some(id) = id.as_ref() {
            let id_bytes = serialized_id_bytes(id);
            let rejection = if id_bytes > MAX_ID_BYTES {
                Some((
                    None,
                    ApiError::InvalidRequest("request id exceeds 512 bytes".to_owned()),
                ))
            } else if inner.outstanding.contains_key(id) {
                Some((
                    Some(id.clone()),
                    ApiError::InvalidRequest("id already outstanding".to_owned()),
                ))
            } else {
                inner.outstanding.insert(id.clone(), ticket);
                None
            };

            if let Some((response_id, error)) = rejection {
                return self.queue_reject_locked(inner, ticket, response_id, error);
            }
        }

        if inner.queued_work < MAX_QUEUED_WORK
            && inner.queued_bytes.saturating_add(bytes) <= MAX_QUEUED_BYTES
        {
            inner.queued_work += 1;
            inner.queued_bytes += bytes;
            inner.queue.push_back(Inbound::Work {
                ticket,
                request,
                bytes,
            });
            self.ready.notify_one();
            return Admission::Accepted;
        }

        match id {
            Some(id) => self.queue_reject_locked(inner, ticket, Some(id), ApiError::IntakeFull),
            None => Admission::Accepted,
        }
    }

    pub(crate) fn reject(&self, id: Option<Id>, error: ApiError) -> Admission {
        let mut inner = self.inner.lock().expect("transport control poisoned");
        if inner.stop || inner.fatal.is_some() {
            return Admission::Halt;
        }
        let ticket = inner.allocate_ticket();
        self.queue_reject_locked(&mut inner, ticket, id, error)
    }

    fn queue_reject_locked(
        &self,
        inner: &mut Inner,
        ticket: Ticket,
        id: Option<Id>,
        error: ApiError,
    ) -> Admission {
        if inner.queued_rejects >= MAX_QUEUED_REJECTS {
            if let Some(id) = id.as_ref()
                && inner.outstanding.get(id) == Some(&ticket)
            {
                inner.outstanding.remove(id);
            }
            inner.stop = true;
            inner.fatal = Some((
                Response::failure(None, ApiError::Flooded),
                "transport rejection partition exhausted".to_owned(),
            ));
            self.ready.notify_one();
            return Admission::Halt;
        }
        inner.queued_rejects += 1;
        inner.queue.push_back(Inbound::Reject { ticket, id, error });
        self.ready.notify_one();
        Admission::Accepted
    }

    pub(crate) fn fatal(&self, response: Response, detail: String) {
        let mut inner = self.inner.lock().expect("transport control poisoned");
        if inner.fatal.is_none() {
            inner.fatal = Some((response, detail));
        }
        inner.stop = true;
        self.ready.notify_one();
    }

    pub(crate) fn next(&self) -> Next {
        let mut inner = self.inner.lock().expect("transport control poisoned");
        loop {
            if let Some(item) = inner.queue.pop_front() {
                match &item {
                    Inbound::Work { bytes, .. } => {
                        inner.queued_work -= 1;
                        inner.queued_bytes -= bytes;
                    }
                    Inbound::Reject { .. } => inner.queued_rejects -= 1,
                    Inbound::Control(_) => {}
                }
                return Next::Inbound(item);
            }
            if let Some((response, detail)) = inner.fatal.take() {
                return Next::Fatal(response, detail);
            }
            if let Some(exit) = inner.reader_exit.clone() {
                return Next::ReaderExited(exit);
            }
            inner = self.ready.wait(inner).expect("transport control poisoned");
        }
    }

    pub(crate) fn begin(&self, ticket: Ticket, id: Option<&Id>) -> Result<CancellationToken, ()> {
        let mut inner = self.inner.lock().expect("transport control poisoned");
        if inner.precancelled.remove(&ticket) {
            return Err(());
        }
        let token = CancellationToken::new();
        inner.executing = Some((ticket, id.cloned(), token.clone()));
        Ok(token)
    }

    pub(crate) fn retire(&self, ticket: Ticket, id: Option<&Id>) {
        let mut inner = self.inner.lock().expect("transport control poisoned");
        if let Some(id) = id
            && inner.outstanding.get(id) == Some(&ticket)
        {
            inner.outstanding.remove(id);
        }
        if inner
            .executing
            .as_ref()
            .is_some_and(|(current, _, _)| *current == ticket)
        {
            inner.executing = None;
        }
        inner.precancelled.remove(&ticket);
    }

    pub(crate) fn stop(&self) {
        let mut inner = self.inner.lock().expect("transport control poisoned");
        inner.stop = true;
        self.ready.notify_all();
    }

    pub(crate) fn reader_exited(&self, exit: ReaderExit) {
        let mut inner = self.inner.lock().expect("transport control poisoned");
        if inner.reader_exit.is_none() {
            inner.reader_exit = Some(exit);
        }
        self.ready.notify_all();
        self.reaped.notify_all();
    }

    pub(crate) fn wait_reaped(&self, deadline: Duration) -> bool {
        let started = Instant::now();
        let mut inner = self.inner.lock().expect("transport control poisoned");
        while inner.reader_exit.is_none() {
            let remaining = deadline.saturating_sub(started.elapsed());
            if remaining.is_zero() {
                return false;
            }
            let (next, timed) = self
                .reaped
                .wait_timeout(inner, remaining)
                .expect("transport control poisoned");
            inner = next;
            if timed.timed_out() && inner.reader_exit.is_none() {
                return false;
            }
        }
        true
    }

    pub(crate) fn drain(&self) -> Vec<Inbound> {
        let mut inner = self.inner.lock().expect("transport control poisoned");
        let drained = inner.queue.drain(..).collect();
        inner.queued_work = 0;
        inner.queued_bytes = 0;
        inner.queued_rejects = 0;
        drained
    }

    #[cfg(test)]
    pub(crate) fn obligation_count(&self) -> usize {
        self.inner
            .lock()
            .expect("transport control poisoned")
            .outstanding
            .len()
    }
    #[cfg(test)]
    pub(crate) fn queued_accounting_for_test(&self) -> (usize, usize) {
        let inner = self.inner.lock().expect("transport control poisoned");
        (inner.queued_work, inner.queued_bytes)
    }
    #[cfg(test)]
    pub(crate) fn next_reader_exit_for_test(&self) -> ReaderExit {
        self.inner
            .lock()
            .expect("transport control poisoned")
            .reader_exit
            .clone()
            .expect("reader exit")
    }
}

impl Inner {
    fn allocate_ticket(&mut self) -> Ticket {
        let ticket = self.next_ticket;
        self.next_ticket = self.next_ticket.wrapping_add(1).max(1);
        ticket
    }

    fn queue_control(&mut self, kind: ControlKind) {
        if !self
            .queue
            .iter()
            .any(|item| matches!(item, Inbound::Control(existing) if *existing == kind))
        {
            self.queue.push_back(Inbound::Control(kind));
        }
    }
}

fn cancel_locked(inner: &mut Inner, id: &Id) {
    let Some(&ticket) = inner.outstanding.get(id) else {
        return;
    };
    if let Some((executing, _, token)) = &inner.executing
        && *executing == ticket
    {
        token.cancel();
    } else {
        inner.precancelled.insert(ticket);
    }
}

fn cancellation_id(request: &Request) -> Option<Id> {
    request
        .params
        .as_ref()?
        .as_object()?
        .get("id")
        .and_then(|value| serde_json::from_value(value.clone()).ok())
}

fn serialized_id_bytes(id: &Id) -> usize {
    match id {
        Id::Number(number) => number.to_string().len(),
        Id::Text(text) => text.len(),
    }
}
