"""Exercise split build/audit control flow without substituting for a kernel proof test."""
import copy
import io
import json
import os
from contextlib import redirect_stderr
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_kernel as kernel

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = (ROOT / ".github/workflows/kernel-lean.yml").read_text(encoding="utf-8")
HEAD = "a" * 40
VERSION = "Lean (version 4.35.0)\n"


class PhaseTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.output = Path(self.temp.name)
        self.contract = {"manifest_sha256": "b" * 64,
                         "modules": {f"Example.M{i:03}": "source" for i in range(201)}}
        self.commands = []
        self.patches = [patch.object(kernel, "validate", return_value=self.contract),
                        patch.object(kernel, "check_dependencies"),
                        patch.object(kernel, "git", return_value=HEAD.encode()),
                        patch.object(kernel, "progress"),
                        patch.object(kernel, "run", side_effect=self.run_command)]
        self.mocks = [p.start() for p in self.patches]

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.temp.cleanup()

    def run_command(self, command, output, name, **kwargs):
        self.commands.append((command, name, kwargs))
        if name == "kernel-audit":
            (output / "audit.json").write_text(json.dumps({"status": "passed", "targets": []}))

    def build(self):
        kernel.build_modules(self.contract, VERSION, self.output)

    def audit(self):
        kernel.audit_modules(self.contract, VERSION, self.output)

    def test_all_module_batches_and_frozen_target_precede_marker(self):
        self.build()
        self.assertEqual([name for _, name, _ in self.commands],
                         ["root-build", "modules-0", "modules-1", "modules-2", "frozen-target-build"])
        built = [arg[1:] for command, name, _ in self.commands if name.startswith("modules-")
                 for arg in command[2:]]
        self.assertEqual(built, sorted(self.contract["modules"]))
        for _, name, options in self.commands[:-1]:
            self.assertTrue(options["audit_metrics"], name)
        marker = json.loads((self.output / "build-complete.json").read_text())
        self.assertEqual(marker["identity"]["head_sha"], HEAD)
        self.assertFalse(marker["acceptance"])
        self.assertFalse((self.output / "audit.json").exists())

    def test_failed_build_removes_previous_success_and_writes_no_new_marker(self):
        for name in ("build-complete.json", "audit.json", "progress.md"):
            (self.output / name).write_text("old success")
        self.mocks[-1].side_effect = RuntimeError("build failed")
        with self.assertRaisesRegex(RuntimeError, "build failed"):
            self.build()
        for name in ("build-complete.json", "audit.json", "progress.md"):
            self.assertFalse((self.output / name).exists())

    def test_source_drift_or_dependency_failure_prevents_marker(self):
        changed = {**self.contract, "manifest_sha256": "c" * 64}
        self.mocks[0].return_value = changed
        with self.assertRaisesRegex(RuntimeError, "changed during compilation"):
            self.build()
        self.assertFalse((self.output / "build-complete.json").exists())
        self.mocks[0].return_value = self.contract
        self.mocks[1].side_effect = RuntimeError("dependency changed")
        with self.assertRaisesRegex(RuntimeError, "dependency changed"):
            self.build()
        self.assertFalse((self.output / "build-complete.json").exists())

    def test_audit_needs_completed_build_at_same_full_identity(self):
        with self.assertRaises(FileNotFoundError):
            self.audit()
        self.assertEqual(self.commands, [])
        self.build()
        original = json.loads((self.output / "build-complete.json").read_text())
        for key, value in [("head_sha", "d" * 40), ("contract_sha256", "e" * 64),
                           ("compiler", "different compiler"), ("modules", [])]:
            bad = copy.deepcopy(original)
            bad["identity"][key] = value
            (self.output / "build-complete.json").write_text(json.dumps(bad))
            self.commands.clear()
            with self.subTest(key=key), self.assertRaisesRegex(RuntimeError, "stale completed-build"):
                self.audit()
            self.assertEqual(self.commands, [])

    def test_completed_build_still_runs_frozen_target_and_full_auditor(self):
        self.build()
        self.commands.clear()
        self.audit()
        self.assertEqual([name for _, name, _ in self.commands], ["frozen-target", "kernel-audit"])
        command = self.commands[-1][0]
        self.assertEqual(command[:5], ["lake", "env", "lean", "--run", "scripts/audit_kernel.lean"])
        spec = json.loads((self.output / "spec.json").read_text())
        self.assertEqual(spec["modules"], sorted(self.contract["modules"]))
        self.assertEqual(json.loads((self.output / "audit.json").read_text())["head_sha"], HEAD)
        self.mocks[3].assert_called_once()

    def test_post_audit_source_drift_still_fails(self):
        self.build()
        changed = {**self.contract, "manifest_sha256": "f" * 64}
        self.mocks[0].side_effect = [self.contract, changed]
        with self.assertRaisesRegex(RuntimeError, "changed during the audit"):
            self.audit()
        self.mocks[3].assert_not_called()

    def test_local_skip_cannot_be_combined_with_a_ci_phase(self):
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            kernel.main(["--skip-build", "--phase", "audit"])


class WorkflowTests(unittest.TestCase):
    def run_swap_step(self, *, available=20 * 1024**3, command_failure=0, record_failure=0):
        """Run the real EXIT trap against harmless stand-ins, never sudo or swapon."""
        steps = re.split(r"^      - name: ", WORKFLOW, flags=re.M)[1:]
        step = next(s for s in steps if s.startswith("Add 8 GiB swap"))
        body = step.split("        run: |\n", 1)[1]
        script = "\n".join(line[10:] for line in body.splitlines()) + "\n"
        bash = "C:/Program Files/Git/bin/bash.exe" if os.name == "nt" else shutil.which("bash")
        self.assertTrue(bash)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "bin").mkdir()
            commands = {
                "free": "exit 0\n",
                "df": "printf 'Avail\\n%s\\n' \"$AVAILABLE\"\n",
                "swapon": "exit 0\n",
                "mktemp": "printf '%s/fake-swap\\n' \"$PWD\"\n",
                "sudo": "printf 'sudo %s\\n' \"$*\" >> trace\nexit \"$COMMAND_FAILURE\"\n",
                "python": "printf 'record %s\\n' \"$*\" >> trace\nexit \"$RECORD_FAILURE\"\n",
            }
            for name, text in commands.items():
                path = root / "bin" / name
                path.write_text("#!/bin/bash\n" + text, encoding="utf-8", newline="\n")
                path.chmod(0o755)
            env = dict(os.environ, AVAILABLE=str(available), COMMAND_FAILURE=str(command_failure),
                       RECORD_FAILURE=str(record_failure))
            env.pop("BASH_ENV", None)
            result = subprocess.run([bash, "--noprofile", "--norc", "-c",
                                     'export PATH="$PWD/bin:$PATH" RUNNER_TEMP="$PWD" GITHUB_STEP_SUMMARY="$PWD/summary"\n' + script],
                                    cwd=root, env=env, capture_output=True, text=True)
            return result, (root / "trace").read_text()

    def test_required_job_keeps_build_upload_audit_order_and_scope(self):
        steps = re.split(r"^      - name: ", WORKFLOW, flags=re.M)[1:]
        names = [s.splitlines()[0] for s in steps]
        sequence = ["Build all kernel modules", "Preserve completed build and resource samples",
                    "Replay all kernel proofs and exact targets", "Upload proof-status evidence"]
        positions = [names.index(n) for n in sequence]
        self.assertEqual(positions, sorted(positions))
        self.assertIn("check_kernel.py --phase build", steps[positions[0]])
        self.assertIn("build/kernel-ci/*-memory.jsonl", steps[positions[1]])
        self.assertNotIn(".lake/build", steps[positions[1]])
        self.assertIn("check_kernel.py --phase audit", steps[positions[2]])
        self.assertNotIn("--skip-build", WORKFLOW)
        condition = "steps.scope.outcome != 'success' || steps.scope.outputs.full_build != 'false'"
        for pos in positions:
            self.assertIn(condition, steps[pos])
        self.assertNotIn("always()", steps[positions[2]])
        self.assertIn("LEAN_NUM_THREADS: '1'", steps[positions[2]])
        self.assertIn("LEAN_NUM_THREADS: '4'", WORKFLOW.split("    steps:", 1)[0])

    def test_swap_settings_unchanged_and_status_preserved_before_build(self):
        self.assertIn('sudo fallocate -l 8G "$swap_file"', WORKFLOW)
        self.assertIn("available < 12 * 1024 * 1024 * 1024", WORKFLOW)
        self.assertIn("trap record_swap_on_exit EXIT", WORKFLOW)
        self.assertLess(WORKFLOW.index("name: Preserve verified swap configuration"),
                        WORKFLOW.index("name: Build all kernel modules"))
        self.assertIn("--record-swap build/kernel-ci/swap-status.json", WORKFLOW)

    def test_swap_exit_trap_records_allocation_and_preserves_command_failure(self):
        result, trace = self.run_swap_step(command_failure=9)
        self.assertEqual(result.returncode, 9, result.stderr)
        self.assertIn("record -B scripts/kernel_diagnostics.py", trace)
        self.assertIn("--allocation added --added-path", trace)
        result, trace = self.run_swap_step(record_failure=7)
        self.assertEqual(result.returncode, 7, result.stderr)

    def test_low_disk_records_skipped_allocation_without_allocating(self):
        result, trace = self.run_swap_step(available=10 * 1024**3)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn("sudo", trace)
        self.assertIn("--allocation skipped-low-disk", trace)


if __name__ == "__main__":
    unittest.main()
