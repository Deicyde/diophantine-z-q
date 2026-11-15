#!/usr/bin/env python3
"""Compare how two copies of ``autoform_audit.py`` read a synthetic build archive.

    python3 .github/tests/benchmark_autoform_audit.py --baseline OLD_COPY --output RESULT.json

Builds gzip and plain archives of synthetic ILean/trace JSON and opaque OLean
bytes in member orders that match, reverse and shuffle the sorted order, then
records for each copy the wall time, the bytes read from the archive file, the
backward seeks on it after the format-detection window, and the peak traced
allocation. The candidate reads an archive in at most two forward passes, so it
makes at most one such seek. Two resource cases follow: an archive whose only
large member is an orphan GNU sparse trace, and one with a large trace the
checks do read. With ``--baseline`` it also checks that both copies give the
same result or the same error message on every fixture of
``test_autoform_audit``. Sizes are fixed by the arguments, not by the machine.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import platform
import random
import statistics
import sys
import tempfile
import time
import tracemalloc
from pathlib import Path

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

import test_autoform_audit as fixtures  # noqa: E402

DETECTION_WINDOW = 512 * 1024


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def outcome(helper, archive: Path, root_package: str) -> str:
    try:
        return json.dumps(list(helper.modules_from_archive(archive, root_package)))
    except helper.AuditInputError as exc:
        return f"error: {exc}"
    except Exception as exc:  # A crash is an outcome too: record its type.
        return f"crash: {type(exc).__name__}: {exc}"


def measure(helper, archive: Path, repeat: int, expected: tuple[str, ...]) -> dict[str, object]:
    times = []
    for _ in range(repeat):
        start = time.perf_counter()
        result = helper.modules_from_archive(archive, fixtures.PACKAGE)
        times.append(time.perf_counter() - start)
        if result != expected:
            raise SystemExit(f"unexpected result from {helper.__name__}")
    with fixtures.recording_archive_reads(archive) as sources:
        helper.modules_from_archive(archive, fixtures.PACKAGE)
    tracemalloc.start()
    helper.modules_from_archive(archive, fixtures.PACKAGE)
    _, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    size = archive.stat().st_size
    read = sum(source.bytes_read for source in sources)
    return {
        "seconds_median": round(statistics.median(times), 4),
        "seconds_min": round(min(times), 4),
        "archive_bytes_read": read,
        "read_amplification": round(read / size, 3),
        "backward_seeks_after_detection": sum(
            1 for source in sources for seek in source.backward_seeks if seek[0] > DETECTION_WINDOW
        ),
        "peak_traced_allocation_bytes": peak,
    }


def benchmark(
    helpers: dict[str, object], modules: int, olean_bytes: int, ilean_padding: int, repeat: int, directory: Path
):
    generator = random.Random(20261115)
    members = []
    for index in range(modules):
        name = f"Bench.M{index:04d}"
        members.extend(
            fixtures.module_members(
                name,
                ilean_data=fixtures.ilean(name, padding=generator.randbytes(ilean_padding // 2).hex()),
                olean_data=generator.randbytes(olean_bytes),
            )
        )
    expected = tuple(sorted(f"Bench.M{index:04d}" for index in range(modules)))
    shuffled = list(members)
    random.Random(1).shuffle(shuffled)
    orders = {"sorted": members, "reversed": members[::-1], "shuffled": shuffled}
    results = []
    for compression in ("gz", ""):
        for order, order_members in orders.items():
            archive = fixtures.write_archive(directory, order_members, compression, f"bench-{order}-{compression}.tar")
            row = {
                "compression": compression or "none",
                "order": order,
                "archive_bytes": archive.stat().st_size,
            }
            for label, helper in helpers.items():
                row[label] = measure(helper, archive, repeat, expected)
            if "baseline" in row:
                row["speedup_median"] = round(
                    row["baseline"]["seconds_median"] / max(row["candidate"]["seconds_median"], 1e-9), 2
                )
            results.append(row)
            archive.unlink()
    return results


def peak_allocation(helper, archive: Path) -> tuple[str, int, float]:
    tracemalloc.start()
    start = time.perf_counter()
    result = outcome(helper, archive, fixtures.PACKAGE)
    seconds = time.perf_counter() - start
    _, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    return result, peak, round(seconds, 4)


def spooled_bytes(helper, archive: Path) -> int | None:
    if not hasattr(helper, "_new_spool"):
        return None
    written = 0
    original = helper._new_spool

    def counting_spool():
        spool = original()
        write = spool.write

        def counting_write(data):
            nonlocal written
            written += len(data)
            return write(data)

        spool.write = counting_write
        return spool

    helper._new_spool = counting_spool
    try:
        outcome(helper, archive, fixtures.PACKAGE)
    finally:
        helper._new_spool = original
    return written


def resources(helpers: dict[str, object], orphan_bytes: int, trace_bytes: int, directory: Path):
    cases = {
        "orphan_sparse_trace": [
            *fixtures.valid_members(),
            fixtures.sparse_member(fixtures.SPARSE_ORPHAN, orphan_bytes),
        ],
        "large_matching_trace": [
            *fixtures.module_members(
                "Demo",
                trace_data=json.dumps(
                    {"synthetic": False, "inputs": ["Module.name: Demo", "Package.id?: (some demo)"],
                     "padding": "x" * trace_bytes}
                ).encode(),
            )
        ],
    }
    report = {}
    for name, members in cases.items():
        archive = fixtures.write_archive(directory, members, "gz", f"resource-{name}.tgz")
        row: dict[str, object] = {"archive_bytes": archive.stat().st_size}
        for label, helper in helpers.items():
            result, peak, seconds = peak_allocation(helper, archive)
            row[label] = {
                "outcome": result,
                "peak_traced_allocation_bytes": peak,
                "seconds_traced": seconds,
                "spooled_bytes": spooled_bytes(helper, archive),
            }
        report[name] = row
        archive.unlink()
    return report


def differential(baseline, candidate, directory: Path) -> dict[str, object]:
    compared = 0
    mismatches = []
    for scenario in fixtures.scenarios():
        for compression in ("", "gz"):
            for order, members in (("forward", scenario.members), ("reversed", scenario.members[::-1])):
                archive = fixtures.write_archive(directory, members, compression, "differential.tar")
                old = outcome(baseline, archive, scenario.root_package)
                new = outcome(candidate, archive, scenario.root_package)
                compared += 1
                if old != new:
                    mismatches.append(
                        {"scenario": scenario.name, "compression": compression or "none", "order": order,
                         "baseline": old, "candidate": new}
                    )
    return {"fixtures_compared": compared, "mismatches": mismatches}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--candidate", type=Path, default=_HERE.parent / "autoform_audit.py")
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--modules", type=int, default=120)
    parser.add_argument("--olean-bytes", type=int, default=32 * 1024)
    parser.add_argument("--ilean-padding", type=int, default=0, help="extra bytes of JSON per ILean")
    parser.add_argument("--repeat", type=int, default=3)
    parser.add_argument("--orphan-trace-bytes", type=int, default=64 * 1024 * 1024)
    parser.add_argument("--large-trace-bytes", type=int, default=32 * 1024 * 1024)
    arguments = parser.parse_args()

    helpers = {"candidate": load(arguments.candidate, "autoform_audit_candidate")}
    if arguments.baseline is not None:
        helpers["baseline"] = load(arguments.baseline, "autoform_audit_baseline")
    with tempfile.TemporaryDirectory() as name:
        directory = Path(name)
        report: dict[str, object] = {
            "python": platform.python_version(),
            "parameters": {
                "modules": arguments.modules,
                "olean_bytes": arguments.olean_bytes,
                "ilean_padding": arguments.ilean_padding,
                "repeat": arguments.repeat,
                "orphan_trace_bytes": arguments.orphan_trace_bytes,
                "large_trace_bytes": arguments.large_trace_bytes,
                "detection_window_bytes": DETECTION_WINDOW,
            },
            "notes": [
                "archive_bytes_read counts bytes read from the archive file itself; a plain tar skips "
                "unread payloads by seeking, so its amplification is below 1 and its backward seeks are cheap.",
                "In a gzip archive every backward seek decompresses the stream again from the start.",
            ],
            "results": benchmark(
                helpers, arguments.modules, arguments.olean_bytes, arguments.ilean_padding, arguments.repeat, directory
            ),
        }
        report["resources"] = resources(
            helpers, arguments.orphan_trace_bytes, arguments.large_trace_bytes, directory
        )
        if "baseline" in helpers:
            report["differential"] = differential(helpers["baseline"], helpers["candidate"], directory)
    text = json.dumps(report, indent=2)
    if arguments.output is not None:
        arguments.output.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
