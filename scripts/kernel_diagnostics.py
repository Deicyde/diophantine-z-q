"""Linux build/audit telemetry and explicit recording of active swap."""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
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
    def __init__(self, pid, output, sample_seconds=5, heartbeat_seconds=30, name="kernel-audit"):
        if not re.fullmatch(r"[a-z0-9-]+", name):
            raise ValueError("Invalid diagnostic phase name")
        self.name = name
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
            print(f"[{self.name} resources] " + json.dumps(sample), flush=True)
            self.next_heartbeat = sample["elapsed_seconds"] + self.heartbeat_seconds

    def worker(self):
        try:
            with (self.output / (self.name + "-memory.jsonl")).open("w", encoding="utf-8") as stream:
                self.sample(stream)
                while not self.stop.wait(self.sample_seconds):
                    self.sample(stream)
                self.sample(stream, final=True)
        except Exception as error:
            # Telemetry is observational. The caller still checks the audit's exit code.
            print(f"[{self.name} resources] telemetry unavailable: {error}", flush=True)

    def __enter__(self):
        self.thread.start()
        return self

    def __exit__(self, *args):
        self.stop.set()
        self.thread.join()


def swap_record(proc=Path("/proc"), added_path=None, requested_bytes=8 * 1024**3,
                allocation="existing", page_size=None):
    """Read kernel-reported active devices. Do not infer activation from swapon's exit alone."""
    if type(requested_bytes) is not int or requested_bytes <= 0:
        raise ValueError("Requested swap size must be a positive integer")
    if allocation == "added" and not added_path:
        raise ValueError("An added-swap record requires its exact path")
    devices = []
    for line in (proc / "swaps").read_text().splitlines()[1:]:
        parts = line.split()
        if len(parts) != 5:
            raise ValueError("Malformed /proc/swaps row")
        path, kind, size, used, priority = parts
        devices.append({"path": path, "type": kind, "size_bytes": int(size) * 1024,
                        "used_bytes": int(used) * 1024, "priority": int(priority)})
    active = [d for d in devices if d["size_bytes"] > 0]
    error = None if active else "No active swap device was verified"
    added = next((d for d in active if d["path"] == str(added_path)), None) if added_path else None
    if added_path:
        page_size = page_size or os.sysconf("SC_PAGE_SIZE")
        if not added or added["size_bytes"] < requested_bytes - page_size:
            error = "The requested additional swap file is absent or smaller than requested"
    return {"schema": "kernel-swap-status/v1", "observed_at": datetime.now(timezone.utc).isoformat(),
            "allocation": allocation, "requested_additional_bytes": requested_bytes,
            "additional_path": str(added_path) if added_path else None,
            "additional_verified": added is not None and error is None,
            "active_total_bytes": sum(d["size_bytes"] for d in active),
            "devices": devices, "verified": error is None, "error": error,
            "host_kib": {k: number(v) for k, v in fields(proc / "meminfo").items()
                         if k in {"MemTotal", "MemAvailable", "SwapTotal", "SwapFree"}}}


def record_swap(output, disk_path, added_path=None, allocation="existing", proc=Path("/proc"), requested_bytes=8 * 1024**3):
    output.parent.mkdir(parents=True, exist_ok=True)
    try:
        record = swap_record(proc, added_path, requested_bytes=requested_bytes, allocation=allocation)
        record["free_disk_bytes"] = shutil.disk_usage(disk_path).free
    except Exception as error:
        record = {"schema": "kernel-swap-status/v1", "verified": False,
                  "allocation": allocation, "error": str(error)}
    output.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record), flush=True)
    if not record["verified"]:
        raise RuntimeError(record["error"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Verify active swap and retain its actual capacity")
    parser.add_argument("--record-swap", type=Path, required=True)
    parser.add_argument("--disk-path", type=Path, required=True)
    parser.add_argument("--added-path", type=Path)
    parser.add_argument("--requested-bytes", type=int, default=8 * 1024**3)
    parser.add_argument("--allocation", choices=("existing", "added", "skipped-low-disk"), required=True)
    args = parser.parse_args()
    record_swap(args.record_swap, args.disk_path, args.added_path, args.allocation,
                requested_bytes=args.requested_bytes)
