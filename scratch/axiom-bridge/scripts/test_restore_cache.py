#!/usr/bin/env python3
"""Synthetic tests for restore_cache.py: tiny archives only, no Lean and no network.

Run from any directory: `python3 -B scratch/axiom-bridge/scripts/test_restore_cache.py`.
Requires the `zstd` command, as the restore helper itself does.
"""
import copy
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import restore_cache  # noqa: E402

REPO = Path(__file__).resolve().parents[3]
COMMITTED = REPO / ".github/axiom-cache.json"
NAME = "synthetic-cache.tar.zst"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def tar_bytes(entries):
    """entries: (name, bytes | None for a directory | ('symlink', target))."""
    out = io.BytesIO()
    with tarfile.open(fileobj=out, mode="w", format=tarfile.PAX_FORMAT) as archive:
        for name, data in entries:
            info = tarfile.TarInfo(name)
            info.mtime = 1700000000
            if data is None:
                info.type, info.mode = tarfile.DIRTYPE, 0o755
                archive.addfile(info)
            elif isinstance(data, tuple):
                info.type, info.linkname = tarfile.SYMTYPE, data[1]
                archive.addfile(info)
            else:
                info.size, info.mode = len(data), 0o4777
                archive.addfile(info, io.BytesIO(data))
    return out.getvalue()


class RestoreTests(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="axiom-restore-test-"))
        self.pins = json.loads(COMMITTED.read_text())["cache_manifest"]

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def entries(self, manifest=None):
        manifest = self.pins if manifest is None else manifest
        return [
            ("AXIOM-CACHE-MANIFEST.json", json.dumps(manifest).encode()),
            ("Stacks", None), ("Stacks/.lake", None), ("Stacks/.lake/build", None),
            ("Stacks/LICENSE", b"stacks license\n"),
            ("Stacks/.lake/build/lib/lean/A.olean", b"A" * 5000),
            ("Mordell", None), ("Mordell/.lake", None), ("Mordell/.lake/build", None),
            ("Mordell/LICENSE", b"mordell license\n"),
            ("Mordell/.lake/build/lib/lean/B.olean", b"B" * 3000),
        ]

    def stage(self, entries, mutate=None):
        raw = tar_bytes(entries)
        archive = subprocess.run(["zstd", "-q", "-c"], input=raw, stdout=subprocess.PIPE,
                                 check=True).stdout
        cut = len(archive) // 2
        chunks = [archive[:cut], archive[cut:]]
        parts = self.tmp / "parts"
        parts.mkdir()
        meta = {
            "release_tag": "axiom-cache-v1",
            "repository": "elliotglazer/diophantine-z-q",
            "archive_name": NAME,
            "archive_bytes": len(archive),
            "archive_sha256": sha(archive),
            "part_limit_bytes": max(len(c) for c in chunks),
            "parts": [],
            "unpacked_tar_bytes": len(raw),
            "minimum_free_disk_bytes": 1,
            "cache_manifest": dict(self.pins),
        }
        sums = [f"{sha(archive)}  {NAME}"]
        for index, chunk in enumerate(chunks):
            name = f"{NAME}.part-{index:03d}"
            (parts / name).write_bytes(chunk)
            meta["parts"].append({"name": name, "bytes": len(chunk), "sha256": sha(chunk)})
            sums.append(f"{sha(chunk)}  {name}")
        (self.tmp / "SHA256SUMS").write_text("\n".join(sums) + "\n")
        if mutate:
            mutate(meta)
        path = self.tmp / "meta.json"
        path.write_text(json.dumps(meta))
        return restore_cache.load_metadata(path), parts

    def test_committed_metadata_is_upstream_and_unchanged_bytes(self):
        meta = restore_cache.load_metadata(COMMITTED)
        self.assertEqual(meta["repository"], "elliotglazer/diophantine-z-q")
        self.assertEqual(meta["archive_sha256"],
                         "4f54433701085fcb631670ff72bff07cf26ab3d47420592b3df5488fe8af8a3a")
        self.assertEqual([p["sha256"] for p in meta["parts"]], [
            "ae4657e24c0da6995e014bbabb164a0ae26671080b18fcbd38b61e0122b2ae99",
            "f365d710f828b1335032afe774b2d7fc24004bd9241d11e94795e19471c7bd78"])
        self.assertEqual(meta["historical_origin"]["repository"], "Deicyde/diophantine-z-q")

    def test_rejects_other_repository_and_bad_parts(self):
        base = json.loads(COMMITTED.read_text())
        for change in (lambda m: m.update(repository="Deicyde/diophantine-z-q"),
                       lambda m: m["parts"][1].update(name=m["archive_name"] + ".part-002"),
                       lambda m: m.update(archive_bytes=m["archive_bytes"] + 1),
                       lambda m: m["parts"][0].update(sha256="A" * 64),
                       lambda m: m["cache_manifest"].update(lean="v4.34.0")):
            meta = copy.deepcopy(base)
            change(meta)
            path = self.tmp / "bad.json"
            path.write_text(json.dumps(meta))
            with self.assertRaises((ValueError, KeyError)):
                restore_cache.load_metadata(path)

    def test_successful_stream_restore_deletes_parts(self):
        meta, parts = self.stage(self.entries())
        dest = self.tmp / "packages"
        restore_cache.restore(meta, parts, dest, self.tmp / "SHA256SUMS")
        self.assertEqual((dest / "Stacks/.lake/build/lib/lean/A.olean").read_bytes(), b"A" * 5000)
        self.assertEqual((dest / "Mordell/LICENSE").read_bytes(), b"mordell license\n")
        mode = (dest / "Stacks/LICENSE").stat().st_mode & 0o7777
        self.assertEqual(mode, 0o755)  # setuid/sticky/group-world write bits masked
        self.assertEqual(list(parts.iterdir()), [])

    def test_bad_part_hash_writes_nothing(self):
        meta, parts = self.stage(self.entries(),
                                 lambda m: m["parts"][1].update(sha256="0" * 64))
        dest = self.tmp / "packages"
        with self.assertRaisesRegex(ValueError, "part SHA-256 mismatch"):
            restore_cache.restore(meta, parts, dest)
        self.assertFalse(dest.exists())
        self.assertEqual(len(list(parts.iterdir())), 2)

    def test_bad_whole_hash_writes_nothing(self):
        meta, parts = self.stage(self.entries(), lambda m: m.update(archive_sha256="0" * 64))
        dest = self.tmp / "packages"
        with self.assertRaisesRegex(ValueError, "concatenated archive"):
            restore_cache.restore(meta, parts, dest)
        self.assertFalse(dest.exists())

    def test_release_checksums_must_match_committed(self):
        meta, parts = self.stage(self.entries())
        sums = self.tmp / "SHA256SUMS"
        sums.write_text(sums.read_text().replace(meta["archive_sha256"], "1" * 64))
        with self.assertRaisesRegex(ValueError, "SHA256SUMS"):
            restore_cache.restore(meta, parts, self.tmp / "packages", sums)

    def test_rejects_unsafe_members(self):
        for bad in (("Stacks/../evil", b"x"), ("Stacks/.lake/build/link", ("symlink", "/etc")),
                    ("Stacks/lakefile.toml", b"x"), ("Other/.lake/build/x", b"x")):
            with self.subTest(member=bad[0]):
                meta, parts = self.stage(self.entries() + [bad])
                with self.assertRaises(ValueError):
                    restore_cache.restore(meta, parts, self.tmp / "packages")
                self.assertEqual(len(list(parts.iterdir())), 2)
            shutil.rmtree(self.tmp)
            self.tmp.mkdir()

    def test_embedded_manifest_pins_must_match(self):
        wrong = dict(self.pins, Mordell="0" * 40)
        meta, parts = self.stage(self.entries(manifest=wrong))
        with self.assertRaisesRegex(ValueError, "pin mismatch"):
            restore_cache.restore(meta, parts, self.tmp / "packages")

    def test_check_pins_reads_bridge_manifest(self):
        meta = restore_cache.load_metadata(COMMITTED)
        restore_cache.check_pins(meta, REPO / "scratch/axiom-bridge")
        bridge = self.tmp / "bridge"
        bridge.mkdir()
        shutil.copy(REPO / "scratch/axiom-bridge/lean-toolchain", bridge)
        manifest = json.loads((REPO / "scratch/axiom-bridge/lake-manifest.json").read_text())
        for package in manifest["packages"]:
            if package["name"] == "Stacks":
                package["rev"] = "0" * 40
        (bridge / "lake-manifest.json").write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, "Stacks"):
            restore_cache.check_pins(meta, bridge)


class AxiomOutputTests(unittest.TestCase):
    def setUp(self):
        import check_axiom_output
        self.check = check_axiom_output
        self.good = "\n".join(
            f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
            for name in sorted(check_axiom_output.EXPECTED))

    def test_accepts_standard_axioms(self):
        self.assertEqual(len(self.check.validate(self.good)), 9)

    def test_rejects_sorry_missing_and_duplicates(self):
        name = sorted(self.check.EXPECTED)[0]
        with self.assertRaises(ValueError):
            self.check.validate(self.good.replace("Quot.sound]", "sorryAx]", 1))
        with self.assertRaises(ValueError):
            self.check.validate("\n".join(self.good.splitlines()[1:]))
        with self.assertRaises(ValueError):
            self.check.validate(self.good + f"\n'{name}' does not depend on any axioms")


if __name__ == "__main__":
    unittest.main(verbosity=2)
