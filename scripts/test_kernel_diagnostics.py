"""Test observational telemetry and preservation of subprocess failures."""
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import time
import unittest

from check_kernel import run
from kernel_diagnostics import AuditDiagnostics, snapshot


class DiagnosticsTests(unittest.TestCase):
    def test_tree_and_cgroup(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            proc, group = root / "proc", root / "cgroup"
            (proc / "self").mkdir(parents=True)
            (group / "job").mkdir(parents=True)
            (proc / "self/cgroup").write_text("0::/job\n")
            (group / "job/memory.current").write_text("4096\n")
            (group / "job/memory.events").write_text("oom 0\noom_kill 0\n")
            (proc / "meminfo").write_text("MemAvailable: 8000 kB\nSwapFree: 4000 kB\n")
            for pid, parent, rss in [(20, 1, 100), (21, 20, 200), (22, 21, 300), (99, 1, 9999)]:
                (proc / str(pid)).mkdir()
                (proc / str(pid) / "status").write_text(
                    f"Name:\tlean\nPPid:\t{parent}\nVmRSS:\t{rss} kB\nVmSwap:\t1 kB\n")
            data = snapshot(20, proc, group)
            self.assertEqual(data["sampled_tree_rss_kib"], 600)
            self.assertEqual(data["sampled_tree_swap_kib"], 3)
            self.assertEqual(data["host_kib"]["MemAvailable"], 8000)
            self.assertEqual(data["cgroup"]["memory.current"], "4096")
            self.assertEqual([p["pid"] for p in data["processes"]], [20, 21, 22])

    def test_missing_metrics_are_unknown(self):
        with tempfile.TemporaryDirectory() as tmp:
            data = snapshot(1, Path(tmp) / "missing", Path(tmp) / "missing")
            self.assertIsNone(data["sampled_tree_rss_kib"])
            self.assertIsNone(data["host_kib"]["MemAvailable"])

    def test_quiet_process_gets_heartbeat_and_flushed_samples(self):
        with tempfile.TemporaryDirectory() as tmp, redirect_stdout(io.StringIO()) as captured:
            output = Path(tmp)
            with AuditDiagnostics(os.getpid(), output, sample_seconds=.02, heartbeat_seconds=.02):
                time.sleep(.15)
                self.assertTrue((output / "kernel-audit-memory.jsonl").read_text().strip())
            samples = [json.loads(line) for line in
                       (output / "kernel-audit-memory.jsonl").read_text().splitlines()]
            self.assertGreaterEqual(len(samples), 2)
            self.assertTrue(samples[-1]["final"])
            self.assertIn("kernel-audit resources", captured.getvalue())

    def test_failure_stays_failure_with_telemetry(self):
        with tempfile.TemporaryDirectory() as tmp, redirect_stdout(io.StringIO()):
            output = Path(tmp)
            with self.assertRaisesRegex(RuntimeError, r"failed \(7\)"):
                run([sys.executable, "-c", "print('before failure'); raise SystemExit(7)"],
                    output, "kernel-audit", cwd=output, audit_metrics=True)
            self.assertEqual(json.loads((output / "kernel-audit-timing.json").read_text())["exit_code"], 7)
            self.assertIn("before failure", (output / "kernel-audit.log").read_text())

    def test_success_stays_success_with_telemetry(self):
        with tempfile.TemporaryDirectory() as tmp, redirect_stdout(io.StringIO()):
            output = Path(tmp)
            run([sys.executable, "-c", "print('done')"], output, "kernel-audit",
                cwd=output, audit_metrics=True)
            self.assertEqual(json.loads((output / "kernel-audit-timing.json").read_text())["exit_code"], 0)


if __name__ == "__main__":
    unittest.main()
