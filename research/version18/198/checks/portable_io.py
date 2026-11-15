"""Command-line paths for the portable finite checkers. No package code is imported."""
import argparse
from pathlib import Path, PurePosixPath
import sys

def parser(description):
    if sys.flags.optimize:
        raise SystemExit("Run without -O or -OO: these finite checks require assertions.")
    p = argparse.ArgumentParser(description=description)
    p.add_argument("--package", type=Path, required=True,
                   help="Extracted H10-quartic198 package directory")
    return p

def file(path):
    path = path.resolve()
    if not path.is_file():
        raise ValueError("Missing input file: " + str(path))
    return path

def package(path):
    path = path.resolve()
    if not path.is_dir():
        raise ValueError("Missing extracted package: " + str(path))
    return path

def output(path, package_path, protected=()):
    path = path.resolve()
    if path.is_relative_to(package_path) or path in protected:
        raise ValueError("Output must not replace a protected input or lie in the source package")
    path.parent.mkdir(parents=True, exist_ok=True)
    return path

def pinned_file(package_path, name):
    parts = PurePosixPath(name).parts
    if not parts or parts[0] != "H10-quartic198" or any(p in ("", ".", "..") for p in parts):
        raise ValueError("Invalid pinned package member: " + name)
    if "\\" in name or ":" in name:
        raise ValueError("Invalid pinned package member: " + name)
    result = package_path.joinpath(*parts[1:]).resolve()
    if not result.is_relative_to(package_path):
        raise ValueError("Pinned member escapes source package")
    return file(result)

def independent_paths():
    p = parser("Independently reconstruct the supplied 204/200/198 finite coefficient data")
    p.add_argument("--pins", type=Path, required=True, help="Original PACKAGE-PINS.json")
    p.add_argument("--archive", type=Path, required=True, help="Original H10-quartic198.zip")
    p.add_argument("--output", type=Path, required=True, help="New JSON result path")
    a = p.parse_args()
    pkg, pins, archive = package(a.package), file(a.pins), file(a.archive)
    return pkg, pins, archive, output(a.output, pkg, (pins, archive))

def roundtrip_paths():
    p = parser("Parse every printed coordinate, integer alias and quadratic row")
    p.add_argument("--rows", type=Path, required=True, help="Standalone q198-rows.tex component")
    p.add_argument("--output", type=Path, required=True, help="New JSON result path")
    a = p.parse_args()
    pkg, rows = package(a.package), file(a.rows)
    return pkg / "circuits/inverse198", rows, output(a.output, pkg, (rows,))

def generator_paths():
    p = parser("Generate the exact frozen unbalanced 198 TeX row component")
    p.add_argument("--output-dir", type=Path, required=True, help="Directory for q198-rows.tex and preview.tex")
    a = p.parse_args()
    pkg, out = package(a.package), a.output_dir.resolve()
    if out.is_relative_to(pkg):
        raise ValueError("Generated output must be outside the source package")
    out.mkdir(parents=True, exist_ok=True)
    return pkg / "circuits/inverse198", out
