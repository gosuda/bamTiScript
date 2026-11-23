use super::*;
use std::io::Read;
use std::process::Command;
use std::process::Output;
use std::process::Stdio;
use std::sync::mpsc;
use std::sync::mpsc::Receiver;
use std::sync::mpsc::TryRecvError;
use std::thread;
use std::time::Duration;

pub(crate) fn capture_process_with_cancel(
    command: &mut Command,
    cancel: &CancellationToken,
) -> io::Result<Option<Output>> {
    configure_managed_process(command);
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let Some(stdout) = child.stdout.take() else {
        let _ = terminate_managed_process(&mut child);
        return Err(io::Error::other("managed child stdout was not piped"));
    };
    let Some(stderr) = child.stderr.take() else {
        let _ = terminate_managed_process(&mut child);
        return Err(io::Error::other("managed child stderr was not piped"));
    };
    let (stdout_reader, stdout_completion) = spawn_child_pipe_reader(stdout);
    let (stderr_reader, stderr_completion) = spawn_child_pipe_reader(stderr);

    let mut status = None;
    let mut stdout_complete = false;
    let mut stderr_complete = false;
    loop {
        if cancel.is_cancelled() {
            let _ = terminate_managed_process(&mut child);
            let _ = join_child_pipe(stdout_reader);
            let _ = join_child_pipe(stderr_reader);
            return Ok(None);
        }
        for (completion, complete) in [
            (&stdout_completion, &mut stdout_complete),
            (&stderr_completion, &mut stderr_complete),
        ] {
            if !*complete {
                match completion.try_recv() {
                    Ok(Ok(())) => *complete = true,
                    Ok(Err(error)) => {
                        let _ = terminate_managed_process(&mut child);
                        let _ = join_child_pipe(stdout_reader);
                        let _ = join_child_pipe(stderr_reader);
                        return Err(error);
                    }
                    Err(TryRecvError::Disconnected) => {
                        let _ = terminate_managed_process(&mut child);
                        let stdout = join_child_pipe(stdout_reader);
                        let stderr = join_child_pipe(stderr_reader);
                        return stdout.and(stderr).map(|_| None);
                    }
                    Err(TryRecvError::Empty) => {}
                }
            }
        }
        if status.is_none() {
            match child.try_wait() {
                Ok(child_status) => status = child_status,
                Err(error) => {
                    let _ = terminate_managed_process(&mut child);
                    let _ = join_child_pipe(stdout_reader);
                    let _ = join_child_pipe(stderr_reader);
                    return Err(error);
                }
            }
        }
        if status.is_some() && stdout_complete && stderr_complete {
            break;
        }
        thread::sleep(Duration::from_millis(5));
    }
    Ok(Some(Output {
        status: status.expect("managed child status is present after loop"),
        stdout: join_child_pipe(stdout_reader)?,
        stderr: join_child_pipe(stderr_reader)?,
    }))
}

pub(super) fn spawn_child_pipe_reader(
    mut pipe: impl Read + Send + 'static,
) -> (
    thread::JoinHandle<io::Result<Vec<u8>>>,
    Receiver<io::Result<()>>,
) {
    let (completion_sender, completion_receiver) = mpsc::channel();
    let reader = thread::spawn(move || {
        let mut bytes = Vec::new();
        let result = pipe.read_to_end(&mut bytes);
        let completion = result
            .as_ref()
            .map(|_| ())
            .map_err(|error| io::Error::new(error.kind(), error.to_string()));
        let _ = completion_sender.send(completion);
        result.map(|_| bytes)
    });
    (reader, completion_receiver)
}

#[cfg(unix)]
pub(super) fn configure_managed_process(command: &mut Command) {
    use std::os::unix::process::CommandExt;
    command.process_group(0);
}

#[cfg(not(unix))]
pub(super) fn configure_managed_process(_command: &mut Command) {}

#[cfg(unix)]
pub(super) fn terminate_managed_process(child: &mut std::process::Child) -> io::Result<()> {
    let group = rustix::process::Pid::from_child(child);
    let terminated = rustix::process::kill_process_group(group, rustix::process::Signal::KILL)
        .map_err(|source| {
            io::Error::other(format!(
                "cannot terminate managed process group {group}: {source}"
            ))
        });
    if terminated.is_err() {
        let _ = child.kill();
    }
    let waited = child.wait().map(|_| ());
    terminated.and(waited)
}

#[cfg(windows)]
pub(super) fn terminate_managed_process(child: &mut std::process::Child) -> io::Result<()> {
    let pid = child.id().to_string();
    let terminated = Command::new("taskkill")
        .args(["/PID", &pid, "/T", "/F"])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .and_then(|status| {
            if status.success() {
                Ok(())
            } else {
                Err(io::Error::other(format!(
                    "cannot terminate managed process tree {pid}: taskkill exited with {status}"
                )))
            }
        });
    if terminated.is_err() {
        let _ = child.kill();
    }
    let waited = child.wait().map(|_| ());
    terminated.and(waited)
}

#[cfg(all(not(unix), not(windows)))]
pub(super) fn terminate_managed_process(child: &mut std::process::Child) -> io::Result<()> {
    child.kill()?;
    child.wait().map(|_| ())
}

pub(super) fn join_child_pipe(
    reader: thread::JoinHandle<io::Result<Vec<u8>>>,
) -> io::Result<Vec<u8>> {
    reader
        .join()
        .map_err(|_| io::Error::other("managed child pipe reader panicked"))?
}
