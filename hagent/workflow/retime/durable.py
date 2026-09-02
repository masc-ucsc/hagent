"""Durable execution for multi-hour EDA/proof jobs.

LangGraph checkpoints graph STATE but does not supervise PROCESSES: it has no
failure detection, no watchdog, no heartbeat.  Our unit of work is a 4-6 hour
Lean job (CVA6 `pmp` took 6.2 h) running unattended, so the process layer has to
come from somewhere else.  This module is that layer.

Jobs run as transient `systemd-run --user` units, which survive the orchestrator
dying, a session ending, or the harness reaping background children.  The graph
never blocks on one: it launches, checkpoints, and a poller node reaps the result
later -- so a crash at any point resumes with the job either still running or its
outcome already on disk.

SENTINEL, NOT systemd, IS THE SOURCE OF TRUTH -- measured, not assumed:

    $ systemctl --user show a-unit-that-never-existed -p Result,ExecMainStatus
    Result=success
    ExecMainStatus=0

A unit that never ran, or that systemd has garbage-collected, is INDISTINGUISHABLE
from one that succeeded unless you also read `LoadState`.  A poller that trusted
`ExecMainStatus` would silently mark an unproven candidate PROVEN.  So the wrapped
command's last act is to write `status.json` with its own exit code, and `poll()`
believes only that file.  systemd supplies supervision and lifetime; it does not
supply verdicts.
"""

from __future__ import annotations

import json
import os
import shlex
import subprocess
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Optional, Sequence

# Job states.  LOST is deliberately distinct from FAILED: a job whose unit is gone
# with no sentinel did not "fail the proof", it failed to report, and an
# unattended loop must retry or escalate rather than record a verdict.
RUNNING = 'running'
DONE = 'done'
LOST = 'lost'
NOT_STARTED = 'not_started'


@dataclass
class JobStatus:
    job_id: str
    state: str
    exit_code: Optional[int] = None
    wall_s: Optional[float] = None
    peak_rss_kb: Optional[int] = None
    unit: Optional[str] = None
    detail: str = ''

    def ok(self) -> bool:
        return self.state == DONE and self.exit_code == 0


class DurableRunner:
    """Launch and poll long jobs as systemd --user units.

    Resource discipline is not optional here: this box is an NFS server whose
    /soe and /mada are exported to other clients, so a heavy unattended job
    degrades machines that are not ours.  Every unit gets nice/ionice/CPUQuota,
    and `exclusive` serializes the classes of job that must not overlap (two
    ~25 GB Lean processes OOM each other, and an OOM-killed run is
    indistinguishable from a proof failure in the log).
    """

    def __init__(self, root: str | Path, cpu_quota: str = '800%',
                 cpuset: str = '0-7', nice: int = 19):
        # MUST be absolute: systemd-run does not inherit the caller's working
        # directory, so a relative root yields
        #   /bin/bash: build/jobs/<id>/run.sh: No such file or directory
        # and a unit that fails instantly with no sentinel -- which the poller
        # correctly but uselessly reports as LOST.
        self.root = Path(root).resolve()
        self.root.mkdir(parents=True, exist_ok=True)
        self.cpu_quota = cpu_quota
        self.cpuset = cpuset
        self.nice = nice

    # ---------------------------------------------------------------- paths
    def jobdir(self, job_id: str) -> Path:
        return self.root / job_id

    def _sentinel(self, job_id: str) -> Path:
        return self.jobdir(job_id) / 'status.json'

    def _unit(self, job_id: str) -> str:
        # systemd unit names are constrained; job ids are ours to keep tame.
        return 'retime-' + job_id.replace('/', '-').replace('_', '-')

    # --------------------------------------------------------------- launch
    def launch(self, job_id: str, argv: Sequence[str], cwd: str | Path,
               env: Optional[dict] = None, exclusive: Optional[str] = None,
               timeout_s: Optional[int] = None) -> JobStatus:
        """Start `argv` detached.  Idempotent: an already-launched job is returned
        as-is rather than started twice, so a graph that replays a checkpointed
        step does not double-spend a 6-hour run."""
        jd = self.jobdir(job_id)
        existing = self.poll(job_id)
        if existing.state != NOT_STARTED:
            return existing

        if exclusive and self.busy(exclusive):
            return JobStatus(job_id, NOT_STARTED,
                             detail=f'exclusive slot {exclusive!r} busy')

        jd.mkdir(parents=True, exist_ok=True)
        log = jd / 'job.log'
        sentinel = self._sentinel(job_id)
        (jd / 'cmd.txt').write_text(' '.join(shlex.quote(a) for a in argv) + '\n')

        # The wrapper writes the sentinel itself.  `%e`/`%M` come from
        # /usr/bin/time so wall and peak RSS are recorded even for a job that
        # exits nonzero -- both are load-bearing when comparing proof cost.
        inner = (
            f'cd {shlex.quote(str(cwd))}\n'
            f'/usr/bin/time -f "RETIME_WALL=%e RETIME_RSS=%M" -o {shlex.quote(str(jd / "time.txt"))} '
            f'{" ".join(shlex.quote(a) for a in argv)} '
            f'>> {shlex.quote(str(log))} 2>&1\n'
            'rc=$?\n'
            f'wall=$(sed -n "s/.*RETIME_WALL=\\([0-9.]*\\).*/\\1/p" {shlex.quote(str(jd / "time.txt"))} | tail -1)\n'
            f'rss=$(sed -n "s/.*RETIME_RSS=\\([0-9]*\\).*/\\1/p" {shlex.quote(str(jd / "time.txt"))} | tail -1)\n'
            # Written last, and atomically, so a torn read can never look like success.
            f'printf \'{{"job_id":"{job_id}","state":"done","exit_code":%s,'
            f'"wall_s":%s,"peak_rss_kb":%s,"finished":%s}}\\n\' '
            f'"$rc" "${{wall:-null}}" "${{rss:-null}}" "$(date +%s)" '
            f'> {shlex.quote(str(sentinel))}.tmp\n'
            f'mv {shlex.quote(str(sentinel))}.tmp {shlex.quote(str(sentinel))}\n'
        )
        (jd / 'run.sh').write_text(inner)

        unit = self._unit(job_id)
        cmd = [
            # NOTE: no `--collect` -- it takes no argument on this systemd
            # (measured: "option '--collect' doesn't allow an argument"), and unit
            # garbage collection is irrelevant to us because the sentinel, not the
            # unit, carries the verdict.
            'systemd-run', '--user', f'--unit={unit}',
            f'--description=retime {job_id}',
            '-p', f'CPUQuota={self.cpu_quota}',
        ]
        if timeout_s:
            cmd += ['-p', f'RuntimeMaxSec={timeout_s}']
        for k, v in (env or {}).items():
            cmd += ['-E', f'{k}={v}']
        cmd += ['nice', '-n', str(self.nice), 'ionice', '-c', '3',
                'taskset', '-c', self.cpuset,
                '/bin/bash', str(jd / 'run.sh')]

        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode != 0:
            return JobStatus(job_id, LOST, unit=unit,
                             detail=f'systemd-run failed: {r.stderr.strip()[:200]}')
        (jd / 'unit.txt').write_text(unit + '\n')
        return JobStatus(job_id, RUNNING, unit=unit)

    # ----------------------------------------------------------------- poll
    def poll(self, job_id: str) -> JobStatus:
        """Sentinel first, always.  systemd is consulted only to tell RUNNING
        from LOST when no sentinel exists yet."""
        jd = self.jobdir(job_id)
        sentinel = self._sentinel(job_id)
        if sentinel.is_file():
            try:
                d = json.loads(sentinel.read_text())
                return JobStatus(job_id, DONE, exit_code=d.get('exit_code'),
                                 wall_s=d.get('wall_s'), peak_rss_kb=d.get('peak_rss_kb'),
                                 unit=d.get('unit'))
            except (json.JSONDecodeError, OSError) as e:
                return JobStatus(job_id, LOST, detail=f'unreadable sentinel: {e}')

        if not (jd / 'unit.txt').is_file():
            return JobStatus(job_id, NOT_STARTED)

        unit = (jd / 'unit.txt').read_text().strip()
        props = self._show(unit)
        # LoadState is the ONLY field that separates "never existed / collected"
        # from "succeeded" -- see the module docstring.
        if props.get('LoadState') == 'not-found' or props.get('ActiveState') in ('inactive', 'failed'):
            return JobStatus(job_id, LOST, unit=unit,
                             detail='unit gone with no sentinel (killed, OOM, or reboot)')
        return JobStatus(job_id, RUNNING, unit=unit)

    def _show(self, unit: str) -> dict:
        r = subprocess.run(
            ['systemctl', '--user', 'show', f'{unit}.service',
             '-p', 'LoadState,ActiveState,SubState,Result,ExecMainStatus'],
            capture_output=True, text=True)
        out = {}
        for line in r.stdout.splitlines():
            if '=' in line:
                k, v = line.split('=', 1)
                out[k] = v
        return out

    # ------------------------------------------------------------ exclusion
    def busy(self, slot: str) -> bool:
        """Is any job holding this exclusive slot still running?"""
        for jd in self.root.iterdir():
            if not jd.is_dir() or not (jd / 'slot.txt').is_file():
                continue
            if jd.joinpath('slot.txt').read_text().strip() != slot:
                continue
            if self.poll(jd.name).state == RUNNING:
                return True
        return False

    def claim(self, job_id: str, slot: str) -> None:
        jd = self.jobdir(job_id)
        jd.mkdir(parents=True, exist_ok=True)
        (jd / 'slot.txt').write_text(slot + '\n')

    def cancel(self, job_id: str) -> None:
        """Stop by unit name.  Never `pkill -f` a pattern -- it also matches the
        launcher shell and can orphan children."""
        jd = self.jobdir(job_id)
        if (jd / 'unit.txt').is_file():
            unit = (jd / 'unit.txt').read_text().strip()
            subprocess.run(['systemctl', '--user', 'stop', f'{unit}.service'],
                           capture_output=True)
            subprocess.run(['systemctl', '--user', 'reset-failed', f'{unit}.service'],
                           capture_output=True)

    def wait(self, job_id: str, poll_s: float = 10.0,
             timeout_s: Optional[float] = None) -> JobStatus:
        """Block until terminal.  For tests and CLI use; the graph does NOT call
        this -- it polls across checkpoints so a crash is survivable."""
        t0 = time.time()
        while True:
            st = self.poll(job_id)
            if st.state in (DONE, LOST, NOT_STARTED):
                return st
            if timeout_s and time.time() - t0 > timeout_s:
                return JobStatus(job_id, RUNNING, detail='wait() timed out')
            time.sleep(poll_s)
