"""Read-only Linux audit telemetry. Missing metrics never bypass proof checks."""
import json
from pathlib import Path
import threading
import time


def fields(path):
    result = {}
    try:
        for line in path.read_text().splitlines():
            key, _, value = line.partition(":")
            if value.strip():
                result[key] = value.strip()
    except (OSError, UnicodeError):
        pass  # A process may exit while /proc is being sampled.
    return result


def number(value):
    try:
        return int(value.split()[0])
    except (AttributeError, ValueError, IndexError):
        return None


def snapshot(pid, proc=Path("/proc"), cgroup=Path("/sys/fs/cgroup")):
    """KiB for /proc values; cgroup v2 values retain their native byte units."""
    statuses = {}
    if proc.is_dir():
        for entry in proc.iterdir():
            if entry.name.isdigit():
                status = fields(entry / "status")
                if status:
                    statuses[int(entry.name)] = status
    included = {pid}
    while True:
        descendants = {n for n, s in statuses.items() if number(s.get("PPid")) in included}
        added = descendants - included
        if not added:
            break
        included.update(added)
    processes = []
    for n in sorted(included & statuses.keys()):
        s = statuses[n]
        processes.append({"pid": n, "name": s.get("Name"),
                          **{k: number(s.get(k)) for k in ("VmRSS", "VmHWM", "VmSwap")}})
    host = fields(proc / "meminfo")
    result = {
        "processes": processes,
        # This is sampled RSS, not PSS: shared pages may be counted more than once.
        "sampled_tree_rss_kib": sum(p["VmRSS"] or 0 for p in processes) if processes else None,
        "sampled_tree_swap_kib": sum(p["VmSwap"] or 0 for p in processes) if processes else None,
        "host_kib": {k: number(host.get(k)) for k in
                     ("MemTotal", "MemAvailable", "SwapTotal", "SwapFree")},
        "cgroup": {},
    }
    # Use this process's cgroup, not a potentially unrelated cgroup-root limit.
    try:
        membership = (proc / "self/cgroup").read_text().splitlines()
        relative = next(line[3:] for line in membership if line.startswith("0::"))
        directory = cgroup / relative.lstrip("/")
        result["cgroup"]["path"] = relative
        for name in ("memory.current", "memory.peak", "memory.max", "memory.swap.current",
                     "memory.swap.max", "memory.events"):
            try:
                result["cgroup"][name] = (directory / name).read_text().strip()
            except OSError:
                pass
    except (OSError, StopIteration, UnicodeError):
        pass
    return result


class AuditDiagnostics:
    """Sample every five seconds; print a heartbeat every thirty seconds."""
    def __init__(self, pid, output, sample_seconds=5, heartbeat_seconds=30):
        self.pid, self.output = pid, output
        self.sample_seconds, self.heartbeat_seconds = sample_seconds, heartbeat_seconds
        self.stop = threading.Event()
        self.start = time.monotonic()
        self.next_heartbeat = 0.0
        self.peak = None
        self.thread = threading.Thread(target=self.worker, daemon=True)

    def sample(self, stream, final=False):
        sample = snapshot(self.pid)
        sample["elapsed_seconds"] = round(time.monotonic() - self.start, 2)
        sample["final"] = final
        rss = sample["sampled_tree_rss_kib"]
        if rss is not None:
            self.peak = max(self.peak or 0, rss)
        sample["sampled_peak_tree_rss_kib"] = self.peak
        stream.write(json.dumps(sample) + "\n")
        stream.flush()
        if final or sample["elapsed_seconds"] >= self.next_heartbeat:
            print("[kernel-audit resources] " + json.dumps(sample), flush=True)
            self.next_heartbeat = sample["elapsed_seconds"] + self.heartbeat_seconds

    def worker(self):
        try:
            with (self.output / "kernel-audit-memory.jsonl").open("w", encoding="utf-8") as stream:
                self.sample(stream)
                while not self.stop.wait(self.sample_seconds):
                    self.sample(stream)
                self.sample(stream, final=True)
        except Exception as error:
            # Telemetry is observational. The caller still checks the audit's exit code.
            print(f"[kernel-audit resources] telemetry unavailable: {error}", flush=True)

    def __enter__(self):
        self.thread.start()
        return self

    def __exit__(self, *args):
        self.stop.set()
        self.thread.join()
