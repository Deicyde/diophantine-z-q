#!/usr/bin/env python3
"""Verify trusted split-cache hashes, then restore without a second archive copy.

Python standard library + zstd; no Lean/Lake invocation. Failed restores are fatal,
never a request to build Axiom dependencies from source. Parts are deleted only
on success. Use a disposable destination after any extraction failure.
"""
import argparse
from contextlib import ExitStack
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import threading

BLOCK = 1024 * 1024
PACKAGES = {"Stacks", "Mordell"}
MANIFEST = "AXIOM-CACHE-MANIFEST.json"


def basename(name):
    if not isinstance(name, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", name):
        raise ValueError(f"unsafe asset basename: {name!r}")
    return name


def positive(value):
    if type(value) is not int or value <= 0:
        raise ValueError(f"expected positive byte count: {value!r}")
    return value


def digest(value):
    if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{64}", value):
        raise ValueError("expected lowercase SHA-256")
    return value


def load_metadata(path):
    meta = json.loads(Path(path).read_text())
    if meta["repository"] != "Deicyde/diophantine-z-q":
        raise ValueError("unexpected cache repository")
    basename(meta["release_tag"])
    archive = basename(meta["archive_name"])
    if not archive.endswith(".tar.zst"):
        raise ValueError("expected .tar.zst archive")
    positive(meta["archive_bytes"])
    digest(meta["archive_sha256"])
    positive(meta["unpacked_tar_bytes"])
    positive(meta["minimum_free_disk_bytes"])
    limit = positive(meta["part_limit_bytes"])
    if not meta["parts"]:
        raise ValueError("no cache parts")
    for index, part in enumerate(meta["parts"]):
        if basename(part["name"]) != f"{archive}.part-{index:03d}":
            raise ValueError("parts must have unique, sequential archive basenames")
        if positive(part["bytes"]) > limit:
            raise ValueError("part exceeds release asset budget")
        digest(part["sha256"])
    if sum(part["bytes"] for part in meta["parts"]) != meta["archive_bytes"]:
        raise ValueError("part sizes do not sum to archive size")
    pins = meta["cache_manifest"]
    if pins["format"] != "axiom-bridge-cache/v1" or pins["platform"] != "linux-x86_64":
        raise ValueError("unsupported cache format/platform")
    if pins["lean"] != "v4.35.0":
        raise ValueError("unexpected Lean version")
    for key in ("lean_commit", "mathlib", "Stacks", "Mordell"):
        if not re.fullmatch(r"[0-9a-f]{40}", pins[key]):
            raise ValueError(f"invalid revision for {key}")
    return meta


def check_pins(meta, bridge):
    bridge = Path(bridge)
    toolchain = (bridge / "lean-toolchain").read_text().strip()
    if toolchain != "leanprover/lean4:" + meta["cache_manifest"]["lean"]:
        raise ValueError("bridge toolchain does not match cache")
    manifest = json.loads((bridge / "lake-manifest.json").read_text())
    if manifest["packagesDir"] != ".lake/packages":
        raise ValueError("unexpected bridge packages directory")
    packages = {package["name"]: package for package in manifest["packages"]}
    for name in ("mathlib", "Stacks", "Mordell"):
        if packages[name]["rev"] != meta["cache_manifest"][name]:
            raise ValueError(f"bridge dependency revision mismatch: {name}")
    print("Bridge Lean and Mathlib/Stacks/Mordell pins match trusted cache metadata.")


def check_checksums(meta, path):
    # Release checksum data is corroboration, NOT the trust root.
    expected = {meta["archive_name"]: meta["archive_sha256"]}
    expected.update({part["name"]: part["sha256"] for part in meta["parts"]})
    actual = {}
    for line in Path(path).read_text().splitlines():
        match = re.fullmatch(r"([0-9a-f]{64}) [ *]([A-Za-z0-9][A-Za-z0-9._-]*)", line)
        if not match or match[2] in actual:
            raise ValueError("malformed or duplicate release checksum entry")
        actual[basename(match[2])] = match[1]
    if actual != expected:
        raise ValueError("release SHA256SUMS differs from committed trusted hashes")


def safe_directory(path, create=True):
    path = Path(os.path.abspath(path))
    current = Path(path.anchor)
    for component in path.parts[1:]:
        current /= component
        if current.is_symlink():
            raise ValueError(f"symlink directory rejected: {current}")
        if create:
            current.mkdir(exist_ok=True)
        if not current.is_dir():
            raise ValueError(f"not a directory: {current}")
    return path


def open_regular(path):
    # O_NOFOLLOW plus fstat also rejects devices/FIFOs and pre-existing hard links.
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
            raise ValueError(f"not a single-link regular file: {path}")
        return os.fdopen(fd, "rb")
    except BaseException:
        os.close(fd)
        raise


def verify_parts(meta, parts_dir, stack):
    parts_dir = safe_directory(parts_dir, create=False)
    files = []
    whole = hashlib.sha256()
    for part in meta["parts"]:
        file = stack.enter_context(open_regular(Path(parts_dir) / part["name"]))
        if os.fstat(file.fileno()).st_size != part["bytes"]:
            raise ValueError(f"part size mismatch: {part['name']}")
        hashed = hashlib.sha256()
        for block in iter(lambda: file.read(BLOCK), b""):
            hashed.update(block)
            whole.update(block)
        if hashed.hexdigest() != part["sha256"]:
            raise ValueError(f"part SHA-256 mismatch: {part['name']}")
        file.seek(0)
        files.append(file)
        print(f"Verified {part['name']}: {part['bytes']} bytes", flush=True)
    if whole.hexdigest() != meta["archive_sha256"]:
        raise ValueError("concatenated archive SHA-256 mismatch")
    print(f"Verified whole archive SHA-256: {whole.hexdigest()}", flush=True)
    return files


def member_path(member):
    name = member.name
    if name.startswith("./"):
        name = name[2:]
    if member.isdir():
        name = name.rstrip("/")
    parts = name.split("/")
    if (not name or "\\" in name or any(ord(c) < 32 for c in name)
            or any(part in ("", ".", "..") for part in parts)):
        raise ValueError(f"unsafe archive path: {member.name!r}")
    if not (member.isdir() or member.isreg()) or member.issparse():
        raise ValueError(f"archive links/special files rejected: {member.name!r}")
    if name == MANIFEST and member.isreg():
        return Path(name)
    if parts[0] not in PACKAGES:
        raise ValueError(f"unexpected archive package: {name}")
    if member.isdir() and (len(parts) == 1 or parts[1:] == [".lake"]):
        return Path(*parts)
    if parts[1:] == ["LICENSE"] and member.isreg():
        return Path(*parts)
    if len(parts) >= 3 and parts[1:3] == [".lake", "build"]:
        if len(parts) == 3 and not member.isdir():
            raise ValueError("build root must be a directory")
        return Path(*parts)
    raise ValueError(f"archive path outside package build/LICENSE: {name}")


class LimitedReader:
    def __init__(self, stream, limit):
        self.stream, self.limit, self.count = stream, limit, 0

    def read(self, size=-1):
        data = self.stream.read(size)
        self.count += len(data)
        if self.count > self.limit:
            raise ValueError("decompressed archive exceeds trusted tar byte count")
        return data


def extract_stream(meta, files, destination):
    root = safe_directory(destination)
    if shutil.disk_usage(root).free < meta["unpacked_tar_bytes"]:
        raise ValueError("insufficient remaining disk for unpacked tar budget")
    proc = subprocess.Popen(["zstd", "-d", "-q", "-c"], stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE)
    errors = []

    def feed():
        try:
            for file in files:
                shutil.copyfileobj(file, proc.stdin, BLOCK)
        except Exception as error:
            errors.append(error)
        finally:
            try:
                proc.stdin.close()
            except OSError as error:
                errors.append(error)

    feeder = threading.Thread(target=feed, daemon=True)
    feeder.start()
    stream = LimitedReader(proc.stdout, meta["unpacked_tar_bytes"])
    seen = set()
    cached_manifest = None
    try:
        with tarfile.open(fileobj=stream, mode="r|", bufsize=BLOCK) as archive:
            for member in archive:
                relative = member_path(member)
                if relative in seen or len(seen) >= 300000:
                    raise ValueError("duplicate path or too many archive members")
                seen.add(relative)
                target = root / relative
                if member.isdir():
                    safe_directory(target)
                    continue
                if member.size < 0 or member.size > meta["unpacked_tar_bytes"]:
                    raise ValueError("invalid archive member size")
                safe_directory(target.parent)
                source = archive.extractfile(member)
                if relative == Path(MANIFEST):
                    if member.size > BLOCK:
                        raise ValueError("cache manifest is too large")
                    data = source.read()
                    cached_manifest = json.loads(data)
                    if any(cached_manifest.get(key) != value
                           for key, value in meta["cache_manifest"].items()):
                        raise ValueError("archive cache manifest pin mismatch")
                    source = io.BytesIO(data)
                fd = os.open(target, os.O_WRONLY | os.O_CREAT | os.O_NOFOLLOW | os.O_NONBLOCK, 0o600)
                with os.fdopen(fd, "wb") as output:
                    info = os.fstat(output.fileno())
                    if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
                        raise ValueError(f"unsafe existing destination: {target}")
                    output.truncate(0)
                    shutil.copyfileobj(source, output, BLOCK)
                    os.fchmod(output.fileno(), member.mode & 0o755)
                os.utime(target, (member.mtime, member.mtime), follow_symlinks=False)
        # Drain zstd, checking its exit status AND exact decompressed tar size.
        while stream.read(BLOCK):
            pass
        feeder.join()
        if proc.wait() != 0 or errors:
            raise ValueError(f"zstd/part streaming failed: {errors}")
        if stream.count != meta["unpacked_tar_bytes"]:
            raise ValueError("unpacked tar byte count mismatch")
        if cached_manifest is None:
            raise ValueError("missing cache manifest")
        for package in PACKAGES:
            if Path(package, "LICENSE") not in seen or not any(
                    path.parts[:3] == (package, ".lake", "build") and len(path.parts) > 3
                    for path in seen):
                raise ValueError(f"missing package build/license: {package}")
    finally:
        if proc.poll() is None:
            proc.terminate()
        proc.stdout.close()
        proc.wait()
        feeder.join()
    print(f"Restored {len(seen)} entries; unpacked tar: {stream.count} bytes.", flush=True)


def restore(meta, parts_dir, destination, checksums=None):
    if checksums is not None:
        check_checksums(meta, checksums)
    with ExitStack() as stack:
        files = verify_parts(meta, parts_dir, stack)
        # No destination writes or decompressor start before the WHOLE hash passes.
        extract_stream(meta, files, destination)
    for part in meta["parts"]:
        (Path(parts_dir) / part["name"]).unlink()
    print("Deleted downloaded parts after successful restore; no full archive copy was created.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--metadata", type=Path, required=True)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--list-assets", action="store_true")
    mode.add_argument("--check-pins", type=Path)
    parser.add_argument("--parts-dir", type=Path)
    parser.add_argument("--packages-dir", type=Path)
    parser.add_argument("--checksums", type=Path)
    args = parser.parse_args()
    meta = load_metadata(args.metadata)
    if args.list_assets:
        print("\n".join([part["name"] for part in meta["parts"]] + ["SHA256SUMS"]))
    elif args.check_pins is not None:
        check_pins(meta, args.check_pins)
    elif args.parts_dir is None or args.packages_dir is None:
        parser.error("restore requires --parts-dir and --packages-dir")
    else:
        restore(meta, args.parts_dir, args.packages_dir, args.checksums)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError) as error:
        print(f"cache restore failed: {error}", file=sys.stderr)
        raise SystemExit(1)
