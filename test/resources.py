#!/usr/bin/env python3
"""Run a command with a process-tree RSS cap and a wall-clock deadline.

Linux /proc and child-subreaper support are required.
This uses RSS rather than RLIMIT_AS: GHC and recent OCaml runtimes reserve
large virtual address ranges. The cap is sampled, not a cgroup hard limit.
"""

import argparse
import ctypes
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


def processes():
    rows = {}
    for path in Path('/proc').glob('[0-9]*/stat'):
        try:
            # A comm field may itself contain spaces and parentheses.
            fields = path.read_text().rsplit(')', 1)[1].split()
            rows[int(path.parent.name)] = (int(fields[1]), max(0, int(fields[21])), fields[19])
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            pass
    return rows


def descendants(root, rows):
    children = {}
    for pid, (parent, _, _) in rows.items():
        children.setdefault(parent, []).append(pid)
    found, pending = set(), [root]
    while pending:
        pid = pending.pop()
        if pid not in found:
            found.add(pid)
            pending.extend(children.get(pid, ()))
    return found


def stop_process_tree(child, known, reaper=None):
    # An unreaped live root still owns its PID. Refresh ancestry before killing
    # it so a child which started after the last RSS sample is included. Never
    # expand ancestry or signal a process group through an already reaped PID.
    running = child is not None and child.poll() is None
    current = processes()
    targets = dict(known)
    if reaper is not None:
        targets.update({pid: current[pid][2] for pid in descendants(reaper, current)
                        if pid != reaper and pid in current})
    if running:
        targets.update({pid: current[pid][2] for pid in descendants(child.pid, current) if pid in current})
    for pid, started_at in targets.items():
        if pid not in current or current[pid][2] != started_at:
            continue
        try:
            os.kill(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    if running:
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def become_subreaper():
    # Detached descendants are reparented to this guard instead of escaping
    # between /proc samples when their immediate parent exits. This changes
    # only this guard process; nested guards keep their own descendant trees.
    libc = ctypes.CDLL(None, use_errno=True)
    control = libc.prctl
    control.argtypes = [ctypes.c_int, ctypes.c_ulong, ctypes.c_ulong,
                        ctypes.c_ulong, ctypes.c_ulong]
    control.restype = ctypes.c_int
    if control(36, 1, 0, 0, 0) != 0:  # Linux PR_SET_CHILD_SUBREAPER
        raise OSError(ctypes.get_errno(), 'cannot establish resource-guard ownership')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quiet', action='store_true', help='report only resource failures')
    parser.add_argument('--rss-mib', type=int, required=True)
    parser.add_argument('--seconds', type=float, required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if args.rss_mib <= 0 or args.seconds <= 0 or not math.isfinite(args.seconds) or not command:
        parser.error('positive limits and a command are required')
    try:
        become_subreaper()
    except (AttributeError, OSError) as error:
        parser.error('Linux child-subreaper support is required: ' + str(error))
    reaper = os.getpid()
    child = None
    started, peak = time.monotonic(), 0
    page_size = os.sysconf('SC_PAGE_SIZE')
    known = {}

    def stop():
        # The cap remains sampled; this refresh also catches new sessions
        # created between the last sample and cancellation.
        stop_process_tree(child, known, reaper)

    def finish_children():
        stop()
        if child is not None:
            child.wait()
        # Reap the command first so waitpid cannot steal Popen's exit status.
        deadline = time.monotonic() + 2
        while True:
            try:
                while os.waitpid(-1, os.WNOHANG)[0]:
                    pass
            except ChildProcessError:
                return
            stop()
            if time.monotonic() >= deadline:
                raise RuntimeError('resource guard could not reap all descendants')
            time.sleep(0.01)

    def interrupted(number, _):
        # An outer timeout sends SIGTERM to this guard, not to the child's
        # separate session. Explicit handlers make that cancellation transitive.
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        finish_children()
        print(f'resource guard: cancelled by signal {number}', file=sys.stderr)
        raise SystemExit(128 + number)

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)

    try:
        child = subprocess.Popen(command, start_new_session=True, env=dict(os.environ, LOL_TEST_RSS_GUARD_PID=str(reaper)))
        while child.poll() is None:
            rows = processes()
            known = {pid: rows[pid][2] for pid in descendants(reaper, rows) if pid != reaper and pid in rows}
            rss = sum(rows[pid][1] for pid in known) * page_size
            peak = max(peak, rss)
            if rss > args.rss_mib * 1024 ** 2 or time.monotonic() - started >= args.seconds:
                reason = 'RSS limit' if rss > args.rss_mib * 1024 ** 2 else 'time limit'
                finish_children()
                print(f'resource guard: {reason}; peak_rss_bytes={peak}', file=sys.stderr)
                return 137 if reason == 'RSS limit' else 124
            time.sleep(0.1)
        finish_children()
        if not args.quiet:
            print(f'resource guard: elapsed={time.monotonic() - started:.3f}s peak_rss_bytes={peak} exit={child.returncode}', file=sys.stderr)
        return child.returncode if child.returncode >= 0 else 128 - child.returncode
    finally:
        finish_children()


if __name__ == '__main__':
    sys.exit(main())
