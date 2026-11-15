#!/usr/bin/env python3
"""Tests for how ``.github/autoform_audit.py`` reads the root-package build archive.

Run from the repository root with ``python3 -m unittest discover -s .github/tests``.
The fixtures are synthetic: ILean and Lake trace JSON written here, and OLean
payloads that are opaque bytes, never real Lean artifacts. Set
``AUTOFORM_AUDIT_UNDER_TEST`` to another copy of the helper to run the same
tests against it.
"""

from __future__ import annotations

import builtins
import contextlib
import gzip
import importlib.util
import io
import json
import os
import random
import tarfile
import tempfile
import unittest
from pathlib import Path, PurePosixPath
from typing import NamedTuple
from unittest import mock

_HELPER = Path(os.environ.get("AUTOFORM_AUDIT_UNDER_TEST", Path(__file__).resolve().parents[1] / "autoform_audit.py"))


def _load_helper():
    spec = importlib.util.spec_from_file_location("autoform_audit_under_test", _HELPER)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


audit = _load_helper()

PACKAGE = "demo"
PREFIX = ".lake/build/lib/lean"
OLEAN_SENTINEL = b"OPAQUE-OLEAN-PAYLOAD-NOT-FOR-CAPTURE"


class Member(NamedTuple):
    """One archive member: a regular file with *data*, or another tar *kind*."""

    name: str
    data: bytes = b""
    kind: bytes = tarfile.REGTYPE
    linkname: str = ""
    pax: tuple[tuple[str, str], ...] = ()


def sparse_member(path: str, real_size: int) -> Member:
    """A GNU sparse (PAX 1.0) regular file of *real_size* bytes that takes about 1 KiB."""

    data = (b"1\n%d\n1\n" % (real_size - 1)).ljust(512, b"\0") + b"\n"
    pax = (
        ("GNU.sparse.major", "1"),
        ("GNU.sparse.minor", "0"),
        ("GNU.sparse.name", path),
        ("GNU.sparse.realsize", str(real_size)),
    )
    return Member(f"GNUSparseFile.0/{PurePosixPath(path).name}", data, pax=pax)


def ilean(module: str, /, **fields: object) -> bytes:
    metadata: dict[str, object] = {
        "version": 4,
        "module": module,
        "directImports": [],
        "decls": {},
        "references": {},
    }
    metadata.update(fields)
    for key, value in list(metadata.items()):
        if value is _DROP:
            del metadata[key]
    return json.dumps(metadata).encode("utf-8")


_DROP = object()


def trace(module: str, package: str = PACKAGE, synthetic: object = False) -> bytes:
    """A Lake-trace-shaped object whose identity strings sit at different depths."""

    value: dict[str, object] = {
        "depHash": "0123456789abcdef",
        "inputs": [
            {"caption": f"Module.name: {module}", "hash": "1"},
            ["nested", [f"Package.id?: (some {package})"]],
        ],
        "log": [],
    }
    if synthetic is not _DROP:
        value["synthetic"] = synthetic
    return json.dumps(value).encode("utf-8")


def module_members(
    module: str,
    path: str | None = None,
    *,
    ilean_data: bytes | None = None,
    trace_data: bytes | None = None,
    olean_data: bytes | None = None,
    with_olean: bool = True,
    with_trace: bool = True,
) -> list[Member]:
    """The ILean, OLean and trace members Lake packs for *module*."""

    stem = path if path is not None else f"{PREFIX}/{module.replace('.', '/')}"
    members = [Member(f"{stem}.ilean", ilean(module) if ilean_data is None else ilean_data)]
    if with_olean:
        members.append(Member(f"{stem}.olean", OLEAN_SENTINEL if olean_data is None else olean_data))
    if with_trace:
        members.append(Member(f"{stem}.trace", trace(module) if trace_data is None else trace_data))
    return members


def write_archive(directory: Path, members: list[Member], compression: str = "", name: str = "") -> Path:
    suffix = ".tgz" if compression == "gz" else ".tar"
    path = directory / (name or f"archive{suffix}")
    with tarfile.open(path, f"w:{compression}", format=tarfile.PAX_FORMAT) as packed:
        for member in members:
            info = tarfile.TarInfo(member.name)
            info.type = member.kind
            info.mtime = 0
            info.mode = 0o644
            if member.pax:
                info.pax_headers = dict(member.pax)
            if member.kind in (tarfile.SYMTYPE, tarfile.LNKTYPE):
                info.linkname = member.linkname or "target"
            if member.kind in (tarfile.REGTYPE, tarfile.AREGTYPE):
                info.size = len(member.data)
                packed.addfile(info, io.BytesIO(member.data))
            else:
                packed.addfile(info)
    return path


def valid_members() -> list[Member]:
    return [
        Member(f"{PREFIX}/", kind=tarfile.DIRTYPE),
        *module_members("Demo"),
        *module_members("Demo.Basic"),
        *module_members("Demo.«Odd name».X", f"{PREFIX}/Demo/Odd name/X"),
        Member("README.md", b"not an artifact"),
        Member(f"{PREFIX}/Demo.olean.hash", b"123"),
        # An OLean or a trace without an ILean is outside the audit, malformed or not.
        Member(f"{PREFIX}/Orphan.olean", b"\x00\x01"),
        Member(f"{PREFIX}/Orphan.trace", b"not json"),
    ]


VALID_MODULES = ("Demo", "Demo.Basic", "Demo.«Odd name».X")
SPARSE_ORPHAN = f"{PREFIX}/Sparse/Orphan.trace"


def orphan_members() -> list[Member]:
    """The valid fixture plus traces the checks never reach, one of them a 64 MiB sparse file."""

    return [
        *valid_members(),
        sparse_member(SPARSE_ORPHAN, 64 * 1024 * 1024),
        # A trace with an OLean but no ILean.
        Member(f"{PREFIX}/Lonely.olean", OLEAN_SENTINEL),
        Member(f"{PREFIX}/Lonely.trace", trace("Lonely")),
    ]


def read_payload_bytes(members: list[Member], limit: int | None = None) -> int:
    """The bytes the checks read: each ILean within *limit*, each trace with that ILean and an OLean."""

    limit = audit._MAX_ILEAN_BYTES if limit is None else limit
    sizes = {member.name: len(member.data) for member in members if member.kind == tarfile.REGTYPE}
    total = 0
    for name, size in sizes.items():
        if name.endswith(".ilean") and size <= limit:
            total += size
        elif name.endswith(".trace"):
            stem = name[: -len(".trace")]
            if sizes.get(f"{stem}.ilean", limit + 1) <= limit and f"{stem}.olean" in sizes:
                total += size
    return total


class Scenario(NamedTuple):
    """A fixture with at most one defect, so its outcome does not depend on member order."""

    name: str
    members: list[Member]
    #: The sorted modules, or the expected error message's prefix.
    expected: tuple[str, ...] | str
    root_package: str = PACKAGE


def _replace(members: list[Member], name: str, **changes: object) -> list[Member]:
    return [member._replace(**changes) if member.name == name else member for member in members]


def scenarios() -> list[Scenario]:
    base = module_members("Demo.Basic")
    ilean_name = f"{PREFIX}/Demo/Basic.ilean"
    olean_name = f"{PREFIX}/Demo/Basic.olean"
    trace_name = f"{PREFIX}/Demo/Basic.trace"

    def bad_ilean(data: bytes) -> list[Member]:
        return _replace(base, ilean_name, data=data)

    def bad_trace(data: bytes) -> list[Member]:
        return _replace(base, trace_name, data=data)

    shape = f"ILean metadata has an invalid {{}} field: {ilean_name}"
    return [
        Scenario("valid", valid_members(), VALID_MODULES),
        Scenario(
            "leading dot components",
            [member._replace(name=f"./{member.name}") for member in base],
            ("Demo.Basic",),
        ),
        Scenario("unsafe parent path", [*base, Member("../escape.ilean", b"{}")], "unsafe ILean archive member path: '../escape.ilean'"),
        Scenario("unsafe inner parent path", [*base, Member("a/../b.trace", b"{}")], "unsafe ILean archive member path: 'a/../b.trace'"),
        Scenario("unsafe absolute path", [*base, Member("/abs/X.olean", b"")], "unsafe ILean archive member path: '/abs/X.olean'"),
        Scenario(
            "duplicate normalized path",
            [*base, Member(f"./{olean_name}", b"again")],
            f"duplicate build archive member: {olean_name}",
        ),
        Scenario(
            "symlink artifact",
            _replace(base, olean_name, kind=tarfile.SYMTYPE, linkname="elsewhere.olean"),
            f"build archive member is not a regular file: {olean_name}",
        ),
        Scenario(
            "hard link artifact",
            [*base, Member(f"{PREFIX}/Copy.olean", kind=tarfile.LNKTYPE, linkname=olean_name)],
            f"build archive member is not a regular file: {PREFIX}/Copy.olean",
        ),
        Scenario(
            "directory artifact",
            [*base, Member(f"{PREFIX}/Dir.trace", kind=tarfile.DIRTYPE)],
            f"build archive member is not a regular file: {PREFIX}/Dir.trace",
        ),
        Scenario(
            "fifo artifact",
            _replace(base, trace_name, kind=tarfile.FIFOTYPE),
            f"build archive member is not a regular file: {trace_name}",
        ),
        Scenario("malformed ILean JSON", bad_ilean(b"{"), f"malformed ILean metadata in {ilean_name}: "),
        Scenario("ILean not UTF-8", bad_ilean(b"\xff\xfe"), f"malformed ILean metadata in {ilean_name}: "),
        Scenario("ILean not an object", bad_ilean(b"[]"), f"ILean metadata is not an object: {ilean_name}"),
        Scenario(
            "ILean module not a string",
            bad_ilean(ilean("Demo.Basic", module=3)),
            f"ILean metadata has an invalid module name: {ilean_name}",
        ),
        Scenario(
            "ILean module syntax",
            bad_ilean(ilean("Demo..Basic")),
            f"ILean metadata has an invalid module name: {ilean_name}",
        ),
        Scenario(
            "ILean version missing",
            bad_ilean(ilean("Demo.Basic", version=_DROP)),
            f"ILean metadata has no integer version: {ilean_name}",
        ),
        Scenario(
            "ILean version string",
            bad_ilean(ilean("Demo.Basic", version="4")),
            f"ILean metadata has no integer version: {ilean_name}",
        ),
        Scenario("ILean decls", bad_ilean(ilean("Demo.Basic", decls=[])), shape.format("decls")),
        Scenario("ILean references", bad_ilean(ilean("Demo.Basic", references=None)), shape.format("references")),
        Scenario("ILean directImports", bad_ilean(ilean("Demo.Basic", directImports={})), shape.format("directImports")),
        Scenario(
            "ILean module does not match path",
            bad_ilean(ilean("Demo.Other")),
            f"ILean module 'Demo.Other' does not match its archive path: {ilean_name}",
        ),
        Scenario(
            "missing OLean",
            module_members("Demo.Basic", with_olean=False),
            f"ILean artifact has no matching OLean: {ilean_name}",
        ),
        Scenario(
            "missing trace",
            module_members("Demo.Basic", with_trace=False),
            f"ILean artifact has no matching Lake trace: {ilean_name}",
        ),
        Scenario("malformed trace JSON", bad_trace(b"{"), f"malformed Lake trace metadata in {trace_name}: "),
        Scenario("trace not an object", bad_trace(b"[false]"), f"invalid Lake trace metadata: {trace_name}"),
        Scenario(
            "synthetic trace",
            bad_trace(trace("Demo.Basic", synthetic=True)),
            f"invalid Lake trace metadata: {trace_name}",
        ),
        Scenario(
            "trace without synthetic",
            bad_trace(trace("Demo.Basic", synthetic=_DROP)),
            f"invalid Lake trace metadata: {trace_name}",
        ),
        Scenario(
            "trace for another module",
            bad_trace(trace("Demo.Other")),
            f"Lake trace does not identify module 'Demo.Basic': {trace_name}",
        ),
        Scenario(
            "trace for another package",
            bad_trace(trace("Demo.Basic", package="dependency")),
            f"Lake trace does not identify root package 'demo': {trace_name}",
        ),
        Scenario(
            "duplicate module",
            [*module_members("Demo", "a/Demo"), *module_members("Demo", "b/Demo")],
            "module 'Demo' has duplicate ILean artifacts: a/Demo.ilean and b/Demo.ilean",
        ),
        Scenario(
            "no ILean",
            [Member(olean_name, OLEAN_SENTINEL), Member(trace_name, trace("Demo.Basic"))],
            "root-package build archive contains no ILean artifacts",
        ),
        Scenario("empty archive", [], "root-package build archive contains no ILean artifacts"),
        Scenario("orphan and sparse traces", orphan_members(), VALID_MODULES),
        Scenario("empty root package", base, "root package name is empty or malformed", root_package=""),
        Scenario("spaced root package", base, "root package name is empty or malformed", root_package="de mo"),
    ]


def outcome(archive: Path, root_package: str = PACKAGE) -> tuple[str, ...] | str:
    try:
        return audit.modules_from_archive(archive, root_package)
    except audit.AuditInputError as exc:
        return f"error: {exc}"


class _RecordingSource:
    """Wraps the archive's file object and records every read and seek on it."""

    def __init__(self, raw):
        self._raw = raw
        self.bytes_read = 0
        self.backward_seeks: list[tuple[int, int]] = []
        self.furthest = 0

    def read(self, size: int = -1) -> bytes:
        data = self._raw.read(size)
        self.bytes_read += len(data)
        self.furthest = max(self.furthest, self._raw.tell())
        return data

    def readinto(self, buffer) -> int:
        count = self._raw.readinto(buffer)
        self.bytes_read += count or 0
        self.furthest = max(self.furthest, self._raw.tell())
        return count

    def seek(self, offset: int, whence: int = 0) -> int:
        before = self._raw.tell()
        after = self._raw.seek(offset, whence)
        if after < before:
            self.backward_seeks.append((self.furthest, after))
        return after

    def tell(self) -> int:
        return self._raw.tell()

    def __enter__(self):
        return self

    def __exit__(self, *exc_info) -> None:
        self._raw.close()

    def __getattr__(self, name: str):
        return getattr(self._raw, name)


@contextlib.contextmanager
def recording_archive_reads(archive: Path):
    """Record reads of *archive* through whatever file object opens it by path.

    ``tarfile`` keeps its own alias of ``open``, which opens a plain archive by name.
    """

    sources: list[_RecordingSource] = []
    original = builtins.open

    def recording_open(file, mode="r", *args, **kwargs):
        handle = original(file, mode, *args, **kwargs)
        if isinstance(file, (str, os.PathLike)) and Path(file) == archive:
            handle = _RecordingSource(handle)
            sources.append(handle)
        return handle

    with mock.patch.object(builtins, "open", recording_open), mock.patch.object(
        tarfile, "bltn_open", recording_open
    ):
        yield sources


class _RecordingSpool(tempfile.SpooledTemporaryFile):
    instances: list["_RecordingSpool"] = []

    def __init__(self, max_size: int):
        super().__init__(max_size=max_size, mode="w+b")
        self.written = bytearray()
        _RecordingSpool.instances.append(self)

    def write(self, data) -> int:
        self.written += data
        return super().write(data)


class ArchiveTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self._directory = tempfile.TemporaryDirectory()
        self.addCleanup(self._directory.cleanup)
        self.directory = Path(self._directory.name)

    def archive(self, members: list[Member], compression: str = "", name: str = "") -> Path:
        return write_archive(self.directory, members, compression, name)


class ScenarioTests(ArchiveTestCase):
    def test_scenarios_plain_gzip_forward_and_reversed(self) -> None:
        for scenario in scenarios():
            for compression in ("", "gz"):
                for order, members in (("forward", scenario.members), ("reversed", scenario.members[::-1])):
                    with self.subTest(scenario=scenario.name, compression=compression or "none", order=order):
                        path = self.archive(members, compression, f"{len(os.listdir(self.directory))}.tar")
                        result = outcome(path, scenario.root_package)
                        if isinstance(scenario.expected, tuple):
                            self.assertEqual(result, scenario.expected)
                        else:
                            self.assertIsInstance(result, str)
                            self.assertTrue(
                                result.startswith(f"error: {scenario.expected}"),
                                f"{result!r} does not start with {scenario.expected!r}",
                            )

    def test_unreadable_archives(self) -> None:
        garbage = self.directory / "garbage.tgz"
        garbage.write_bytes(b"this is neither tar nor gzip" * 40)
        missing = self.directory / "missing.tgz"
        for path in (garbage, missing):
            with self.subTest(path=path.name):
                with self.assertRaisesRegex(audit.AuditInputError, "^cannot read root-package build archive: "):
                    audit.modules_from_archive(path, PACKAGE)

    def test_truncated_archives_fail_cleanly(self) -> None:
        members = [*valid_members(), Member(f"{PREFIX}/Large.olean", random.Random(1).randbytes(256 * 1024))]
        for compression in ("", "gz"):
            with self.subTest(compression=compression or "none"):
                path = self.archive(members, compression, f"whole-{compression}.tar")
                data = path.read_bytes()
                cut = self.directory / f"cut-{compression}.tar"
                cut.write_bytes(data[: len(data) // 2])
                with self.assertRaisesRegex(audit.AuditInputError, "^cannot read root-package build archive: "):
                    audit.modules_from_archive(cut, PACKAGE)


class PrecedenceTests(ArchiveTestCase):
    """The first error reported is the one the two-phase reading reported."""

    def assert_error_in_every_order(self, members: list[Member], expected: str) -> None:
        orders = [members, members[::-1]]
        for seed in range(3):
            shuffled = list(members)
            random.Random(seed).shuffle(shuffled)
            orders.append(shuffled)
        for index, order in enumerate(orders):
            for compression in ("", "gz"):
                with self.subTest(order=index, compression=compression or "none"):
                    path = self.archive(order, compression, f"order-{index}-{compression}.tar")
                    result = outcome(path)
                    self.assertIsInstance(result, str)
                    self.assertTrue(result.startswith(f"error: {expected}"), result)

    def test_member_checks_precede_metadata_checks(self) -> None:
        # The broken ILean comes first in the archive and in sorted order, but
        # every path and type check covers the whole archive before any ILean is read.
        members = [
            *module_members("A", ilean_data=b"{"),
            Member(f"{PREFIX}/Z.olean", kind=tarfile.SYMTYPE, linkname="A.olean"),
        ]
        path = self.archive(members, "gz")
        self.assertEqual(
            outcome(path), f"error: build archive member is not a regular file: {PREFIX}/Z.olean"
        )

    def test_first_member_defect_in_archive_order(self) -> None:
        members = [
            Member(f"{PREFIX}/Z.olean", kind=tarfile.SYMTYPE, linkname="x"),
            Member("../A.ilean", b"{}"),
        ]
        self.assertEqual(
            outcome(self.archive(members)), f"error: build archive member is not a regular file: {PREFIX}/Z.olean"
        )
        self.assertEqual(
            outcome(self.archive(members[::-1], name="reversed.tar")),
            "error: unsafe ILean archive member path: '../A.ilean'",
        )

    def test_metadata_errors_in_sorted_order(self) -> None:
        members = [*module_members("B", ilean_data=b"[]"), *module_members("A", trace_data=b"{")]
        self.assert_error_in_every_order(members, f"malformed Lake trace metadata in {PREFIX}/A.trace: ")

    def test_oversized_ilean_reported_at_its_sorted_turn(self) -> None:
        members = [
            *module_members("B", ilean_data=b"{"),
            *module_members("A", ilean_data=ilean("A", padding="x" * 512)),
        ]
        with mock.patch.object(audit, "_MAX_ILEAN_BYTES", 256):
            self.assert_error_in_every_order(members, f"ILean archive member is unexpectedly large: {PREFIX}/A.ilean")

    def test_size_limit_is_inclusive(self) -> None:
        data = ilean("A")
        path = self.archive(module_members("A", ilean_data=data))
        with mock.patch.object(audit, "_MAX_ILEAN_BYTES", len(data)):
            self.assertEqual(outcome(path), ("A",))
        with mock.patch.object(audit, "_MAX_ILEAN_BYTES", len(data) - 1):
            self.assertEqual(outcome(path), f"error: ILean archive member is unexpectedly large: {PREFIX}/A.ilean")

    def test_default_size_limit_unchanged(self) -> None:
        self.assertEqual(audit._MAX_ILEAN_BYTES, 16 * 1024 * 1024)


class DeterminismTests(ArchiveTestCase):
    def test_output_independent_of_member_order(self) -> None:
        members = [member for index in range(12) for member in module_members(f"Demo.M{index:02d}")]
        expected = tuple(sorted(f"Demo.M{index:02d}" for index in range(12)))
        for seed in range(5):
            shuffled = list(members)
            random.Random(seed).shuffle(shuffled)
            for compression in ("", "gz"):
                with self.subTest(seed=seed, compression=compression or "none"):
                    path = self.archive(shuffled, compression, f"{seed}-{compression}.tar")
                    self.assertEqual(outcome(path), expected)
                    self.assertEqual(outcome(path), expected)


class TraversalTests(ArchiveTestCase):
    """The archive is read in at most two forward passes, and OLean payloads are never read."""

    DETECTION_WINDOW = 512 * 1024

    def large_members(self, order: str) -> tuple[list[Member], tuple[str, ...]]:
        generator = random.Random(7)
        members: list[Member] = []
        for index in range(48):
            members.extend(
                module_members(f"Demo.M{index:02d}", olean_data=generator.randbytes(48 * 1024))
            )
        if order == "reversed":
            members.reverse()
        elif order == "shuffled":
            generator.shuffle(members)
        return members, tuple(sorted(f"Demo.M{index:02d}" for index in range(48)))

    def read_archive(self, order: str, compression: str) -> tuple[int, int, int]:
        """Return the archive size, the bytes read from it, and its backward seeks after detection."""

        members, expected = self.large_members(order)
        path = self.archive(members, compression, f"large-{order}-{compression}.tar")
        size = path.stat().st_size
        self.assertGreater(size, 2 * 1024 * 1024)
        with recording_archive_reads(path) as sources:
            self.assertEqual(audit.modules_from_archive(path, PACKAGE), expected)
        self.assertTrue(sources)
        # Format detection may rewind near the start; only later rewinds count.
        late = sum(1 for source in sources for seek in source.backward_seeks if seek[0] > self.DETECTION_WINDOW)
        return size, sum(source.bytes_read for source in sources), late

    def test_one_pass_when_traces_follow_their_ilean_and_olean(self) -> None:
        for compression in ("", "gz"):
            with self.subTest(compression=compression or "none"):
                size, read, late = self.read_archive("sorted", compression)
                self.assertEqual(late, 0)
                self.assertLessEqual(read, size + self.DETECTION_WINDOW)

    def test_at_most_two_forward_passes(self) -> None:
        for order in ("reversed", "shuffled"):
            for compression in ("", "gz"):
                with self.subTest(order=order, compression=compression or "none"):
                    size, read, late = self.read_archive(order, compression)
                    # Traces that come before their ILean or OLean need the second pass.
                    self.assertEqual(late, 1)
                    self.assertLessEqual(read, 2 * size + self.DETECTION_WINDOW)

    def extracted_names(self, path: Path) -> tuple[object, list[str]]:
        extracted: list[str] = []
        original = tarfile.TarFile.extractfile

        def recording_extractfile(self, member):
            extracted.append(member.name if isinstance(member, tarfile.TarInfo) else member)
            return original(self, member)

        with mock.patch.object(tarfile.TarFile, "extractfile", recording_extractfile):
            result = outcome(path)
        return result, extracted

    def test_olean_payloads_never_extracted(self) -> None:
        members, expected = self.large_members("shuffled")
        result, extracted = self.extracted_names(self.archive(members, "gz"))
        self.assertEqual(result, expected)
        self.assertTrue(extracted)
        self.assertFalse([name for name in extracted if name.endswith(".olean")])
        # Each captured payload is read exactly once.
        self.assertEqual(len(extracted), len(set(extracted)))

    def test_orphan_traces_never_extracted(self) -> None:
        members = orphan_members()
        for compression in ("", "gz"):
            for order, ordered in (("forward", members), ("reversed", members[::-1])):
                with self.subTest(compression=compression or "none", order=order):
                    path = self.archive(ordered, compression, f"orphans-{order}-{compression}.tar")
                    self.assertLess(path.stat().st_size, 64 * 1024)
                    result, extracted = self.extracted_names(path)
                    self.assertEqual(result, VALID_MODULES)
                    self.assertFalse([name for name in extracted if "Orphan" in name or "Lonely" in name])
                    self.assertEqual(len(extracted), 2 * len(VALID_MODULES))


@unittest.skipUnless(hasattr(audit, "_new_spool"), "the helper under test has no capture spool")
class SpoolTests(ArchiveTestCase):
    def run_with_spool(self, path: Path, max_size: int) -> tuple[object, list[_RecordingSpool], list[str]]:
        _RecordingSpool.instances = []
        spill = self.directory / "spill"
        spill.mkdir(exist_ok=True)
        with mock.patch.object(audit, "_new_spool", lambda: _RecordingSpool(max_size)), mock.patch.object(
            tempfile, "tempdir", str(spill)
        ):
            result = outcome(path)
        return result, list(_RecordingSpool.instances), os.listdir(spill)

    def test_spool_holds_only_ilean_and_trace_payloads(self) -> None:
        members = valid_members()
        path = self.archive(members, "gz")
        result, spools, leftovers = self.run_with_spool(path, 1 << 20)
        self.assertEqual(result, VALID_MODULES)
        self.assertEqual(len(spools), 1)
        self.assertEqual(len(spools[0].written), read_payload_bytes(members))
        self.assertNotIn(OLEAN_SENTINEL, bytes(spools[0].written))
        self.assertTrue(spools[0].closed)
        self.assertEqual(leftovers, [])

    def test_orphan_traces_not_spooled(self) -> None:
        members = orphan_members()
        for order, ordered in (("forward", members), ("reversed", members[::-1])):
            with self.subTest(order=order):
                path = self.archive(ordered, "gz", f"orphans-{order}.tgz")
                result, spools, leftovers = self.run_with_spool(path, 1 << 20)
                self.assertEqual(result, VALID_MODULES)
                self.assertEqual(len(spools[0].written), read_payload_bytes(members))
                self.assertNotIn(b"Lonely", bytes(spools[0].written))
                self.assertFalse(spools[0]._rolled)
                self.assertEqual(leftovers, [])

    def test_trace_without_olean_not_spooled(self) -> None:
        members = module_members("A", with_olean=False)
        result, spools, _ = self.run_with_spool(self.archive(members[::-1]), 1 << 20)
        self.assertEqual(result, f"error: ILean artifact has no matching OLean: {PREFIX}/A.ilean")
        self.assertEqual(bytes(spools[0].written), members[0].data)

    def test_oversized_ilean_not_captured(self) -> None:
        path = self.archive(module_members("A", ilean_data=ilean("A", padding="x" * 4096)))
        with mock.patch.object(audit, "_MAX_ILEAN_BYTES", 1024):
            result, spools, _ = self.run_with_spool(path, 1 << 20)
        self.assertTrue(str(result).startswith("error: ILean archive member is unexpectedly large"))
        self.assertLess(len(spools[0].written), 1024)

    def test_spill_to_disk_and_cleanup(self) -> None:
        members = [member for index in range(20) for member in module_members(f"Demo.M{index:02d}")]
        broken = [*members, *module_members("Demo.Z", trace_data=b"{")]
        nonregular = [*members, Member(f"{PREFIX}/Z.olean", kind=tarfile.SYMTYPE, linkname="x")]
        cases = (
            ("success", members, tuple(sorted(f"Demo.M{index:02d}" for index in range(20)))),
            ("validation error", broken, f"error: malformed Lake trace metadata in {PREFIX}/Demo/Z.trace: "),
            ("traversal error", nonregular, "error: build archive member is not a regular file"),
        )
        for label, case_members, expected in cases:
            for compression in ("", "gz"):
                with self.subTest(case=label, compression=compression or "none"):
                    path = self.archive(case_members, compression, f"{label}-{compression}.tar")
                    result, spools, leftovers = self.run_with_spool(path, 512)
                    if isinstance(expected, tuple):
                        self.assertEqual(result, expected)
                    else:
                        self.assertTrue(str(result).startswith(expected), result)
                    self.assertEqual(len(spools), 1)
                    self.assertTrue(spools[0]._rolled, "the spool should have moved to a file")
                    self.assertTrue(spools[0].closed)
                    self.assertEqual(leftovers, [])


class CommandLineTests(ArchiveTestCase):
    def test_writes_probe(self) -> None:
        path = self.archive(valid_members(), "gz")
        probe = self.directory / "probe.lean"
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            self.assertEqual(audit.main([PACKAGE, str(path), str(probe)]), 0)
        self.assertEqual(stdout.getvalue(), "prepared kernel-trust audit for 3 root-package module(s)\n")
        text = probe.read_text(encoding="utf-8")
        self.assertTrue(text.startswith(audit._PROBE + "\nrun_cmd autoformAuditStrict "))
        self.assertEqual(text, audit.render_probe(VALID_MODULES))

    def test_reports_archive_error(self) -> None:
        path = self.archive(module_members("Demo", with_trace=False))
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr):
            self.assertEqual(audit.main([PACKAGE, str(path), str(self.directory / "probe.lean")]), 1)
        self.assertEqual(
            stderr.getvalue(), f"error: ILean artifact has no matching Lake trace: {PREFIX}/Demo.ilean\n"
        )
        self.assertFalse((self.directory / "probe.lean").exists())


if __name__ == "__main__":
    unittest.main()
