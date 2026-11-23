"""Exercise child cleanup in the Linux optimization measurement runner."""

from __future__ import annotations

import errno
import os
import select
import signal
import subprocess
import sys
import time
from contextlib import suppress
from dataclasses import dataclass
from pathlib import Path

import pytest

import compare_optimization as comparison

pytestmark: pytest.MarkDecorator = pytest.mark.skipif(
    sys.platform != "linux",
    reason="the comparison runner requires Linux pidfds",
)

_DESCENDANT_PROGRAM: str = """
import subprocess
import sys
import time
from pathlib import Path

descendant = subprocess.Popen(
    (sys.executable, "-c", "import time; time.sleep(30)")
)
ready = Path(sys.argv[1])
pending = ready.with_suffix(".pending")
pending.write_text(str(descendant.pid), encoding="ascii")
pending.replace(ready)
time.sleep(30)
"""


@dataclass(frozen=True, slots=True)
class ProcessHandle:
    pid: int
    descriptor: int


def _exit_ready(handle: ProcessHandle, timeout_ms: int) -> bool:
    poller = select.poll()
    poller.register(handle.descriptor, select.POLLIN)
    return any(
        events & (select.POLLIN | select.POLLHUP)
        for _, events in poller.poll(timeout_ms)
    )


def _kill_and_close(handle: ProcessHandle) -> None:
    try:
        with suppress(ProcessLookupError):
            signal.pidfd_send_signal(handle.descriptor, signal.SIGKILL)
    finally:
        os.close(handle.descriptor)


def _assert_reaped(pid: int) -> None:
    with pytest.raises(ChildProcessError):
        os.waitpid(pid, os.WNOHANG)


def _read_published_pid(path: Path) -> int:
    deadline = time.monotonic() + 5.0
    while True:
        try:
            return int(path.read_text(encoding="ascii"))
        except FileNotFoundError:
            if time.monotonic() >= deadline:
                raise TimeoutError("child did not publish its descendant PID")
            time.sleep(0.005)


def test_logged_captures_short_child_output_and_reaps(tmp_path: Path) -> None:
    prefix = tmp_path / "success"
    command = (
        sys.executable,
        "-c",
        "import os, sys; "
        "print(os.getpid()); "
        "print('ready'); "
        "print('detail', file=sys.stderr)",
    )

    elapsed = comparison.logged(
        command,
        tmp_path,
        dict(os.environ),
        prefix,
        deadline=time.monotonic() + 10.0,
        maximum_seconds=5.0,
    )

    pid_text, message = (
        prefix.with_suffix(".stdout.log").read_text(encoding="utf-8").splitlines()
    )
    assert message == "ready"
    assert prefix.with_suffix(".stderr.log").read_bytes() == b"detail\n"
    assert elapsed > 0
    _assert_reaped(int(pid_text))


def test_logged_timeout_kills_group_and_reaps(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    ready = tmp_path / "descendant.pid"
    parent_pids: list[int] = []
    descendants: list[ProcessHandle] = []
    real_pidfd_open = os.pidfd_open

    def open_after_descendant_is_ready(pid: int, flags: int = 0) -> int:
        parent_pids.append(pid)
        descendant_pid = _read_published_pid(ready)
        descendants.append(
            ProcessHandle(
                descendant_pid,
                real_pidfd_open(descendant_pid),
            )
        )
        return real_pidfd_open(pid, flags)

    monkeypatch.setattr(comparison.os, "pidfd_open", open_after_descendant_is_ready)
    command = (sys.executable, "-c", _DESCENDANT_PROGRAM, str(ready))
    started = time.monotonic()
    try:
        with pytest.raises(subprocess.TimeoutExpired):
            comparison.logged(
                command,
                tmp_path,
                dict(os.environ),
                tmp_path / "timeout",
                deadline=time.monotonic() + 10.0,
                maximum_seconds=1.0,
            )

        assert time.monotonic() - started < 10.0
        assert parent_pids
        assert descendants
        _assert_reaped(parent_pids[0])
        assert _exit_ready(descendants[0], 3000), "descendant survived timeout"
    finally:
        for handle in descendants:
            _kill_and_close(handle)


def test_logged_pidfd_setup_failure_kills_and_reaps(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    children: list[ProcessHandle] = []
    real_pidfd_open = os.pidfd_open

    def fail_pidfd_open(pid: int, flags: int = 0) -> int:
        children.append(ProcessHandle(pid, real_pidfd_open(pid, flags)))
        raise OSError(errno.EMFILE, "forced pidfd_open failure")

    monkeypatch.setattr(comparison.os, "pidfd_open", fail_pidfd_open)
    command = (sys.executable, "-c", "import time; time.sleep(30)")
    started = time.monotonic()
    try:
        with pytest.raises(OSError, match="forced pidfd_open failure") as caught:
            comparison.logged(
                command,
                tmp_path,
                dict(os.environ),
                tmp_path / "setup-failure",
                deadline=time.monotonic() + 10.0,
                maximum_seconds=5.0,
            )

        assert caught.value.errno == errno.EMFILE
        assert time.monotonic() - started < 10.0
        assert children
        assert _exit_ready(children[0], 0), "child survived setup failure"
        _assert_reaped(children[0].pid)
    finally:
        for handle in children:
            _kill_and_close(handle)
