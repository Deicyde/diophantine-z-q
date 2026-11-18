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
from unittest.mock import patch

from check_kernel import run
from kernel_diagnostics import AuditDiagnostics, snapshot, swap_record, record_swap


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

    def test_build_phases_have_separate_resource_files(self):
        with tempfile.TemporaryDirectory() as tmp, redirect_stdout(io.StringIO()) as captured:
            output = Path(tmp)
            for name in ("root-build", "modules-0"):
                with AuditDiagnostics(os.getpid(), output, name=name):
                    pass
                samples = [json.loads(line) for line in (output / (name + "-memory.jsonl")).read_text().splitlines()]
                self.assertTrue(samples[-1]["final"])
                self.assertIn(f"[{name} resources]", captured.getvalue())
            self.assertFalse((output / "kernel-audit-memory.jsonl").exists())

    def test_swap_capacity_and_additional_file_are_verified(self):
        with tempfile.TemporaryDirectory() as tmp:
            proc = Path(tmp)
            (proc / "swaps").write_text("Filename Type Size Used Priority\n/new file 8388604 0 -2\n")
            result = swap_record(proc, "/new", allocation="added", page_size=4096)
            self.assertTrue(result["verified"])
            self.assertTrue(result["additional_verified"])
            self.assertEqual(result["active_total_bytes"], 8 * 1024**3 - 4096)
            self.assertFalse(swap_record(proc, "/missing", page_size=4096)["verified"])
            (proc / "swaps").write_text("Filename Type Size Used Priority\n/new file 100 0 -2\n")
            self.assertFalse(swap_record(proc, "/new", page_size=4096)["verified"])

    def test_low_disk_retains_and_reports_existing_swap(self):
        with tempfile.TemporaryDirectory() as tmp:
            proc = Path(tmp)
            (proc / "swaps").write_text("Filename Type Size Used Priority\n/old file 3145728 20 -2\n")
            result = swap_record(proc, allocation="skipped-low-disk")
            self.assertTrue(result["verified"])
            self.assertFalse(result["additional_verified"])
            self.assertEqual(result["active_total_bytes"], 3 * 1024**3)
            self.assertEqual(result["allocation"], "skipped-low-disk")

    def test_requested_24_gib_rejects_old_8_gib_and_records_real_capacity(self):
        with tempfile.TemporaryDirectory() as tmp, redirect_stdout(io.StringIO()):
            proc = Path(tmp)
            output = proc / "result.json"
            requested = 24 * 1024**3
            # Only a single header page may be missing from the usable size.
            for kib, accepted in [(8388604, False), (25165819, False), (25165820, True), (25165824, True)]:
                (proc / "swaps").write_text(f"Filename Type Size Used Priority\n/new file {kib} 0 -2\n")
                result = swap_record(proc, "/new", requested_bytes=requested,
                                     allocation="added", page_size=4096)
                self.assertEqual(result["verified"], accepted)
                self.assertEqual(result["requested_additional_bytes"], requested)
                self.assertEqual(result["active_total_bytes"], kib * 1024)
            with patch("kernel_diagnostics.os.sysconf", return_value=4096, create=True):
                record_swap(output, proc, "/new", "added", proc=proc, requested_bytes=requested)
            self.assertEqual(json.loads(output.read_text())["requested_additional_bytes"], requested)

    def test_requested_swap_size_is_positive_and_integral(self):
        for value in [0, -1, True, 24.0, "24"]:
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "positive integer"):
                swap_record(requested_bytes=value)

    def test_missing_swap_fails_after_record_is_written(self):
        with tempfile.TemporaryDirectory() as tmp, redirect_stdout(io.StringIO()):
            proc = Path(tmp)
            (proc / "swaps").write_text("Filename Type Size Used Priority\n")
            output = proc / "result.json"
            with self.assertRaisesRegex(RuntimeError, "No active swap"):
                record_swap(output, proc, proc=proc)
            self.assertFalse(json.loads(output.read_text())["verified"])

    def test_unreadable_swap_fails_with_a_record(self):
        with tempfile.TemporaryDirectory() as tmp, redirect_stdout(io.StringIO()):
            proc = Path(tmp)
            output = proc / "result.json"
            with self.assertRaises(RuntimeError):
                record_swap(output, proc, proc=proc)
            self.assertFalse(json.loads(output.read_text())["verified"])


if __name__ == "__main__":
    unittest.main()
