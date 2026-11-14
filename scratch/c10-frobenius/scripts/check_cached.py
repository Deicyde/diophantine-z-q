#!/usr/bin/env python3
"""Compile one local proof file against explicitly supplied, existing cached artifacts."""
import argparse
import os
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--toolchain', type=Path, required=True)
parser.add_argument('--mathlib', type=Path, required=True)
parser.add_argument('--stacks', type=Path, required=True)
parser.add_argument('--dependency-lib', type=Path, action='append', default=[])
parser.add_argument('--olean', type=Path, help='Write the checked module to this local output path')
parser.add_argument('--source-root', type=Path,
                    help='Explicit package root for native nested module names; no dependency build')
parser.add_argument('source', type=Path)
args = parser.parse_args()

lean = args.toolchain.resolve() / 'bin/lean'
commit = subprocess.check_output([str(lean), '--githash'], text=True).strip()
if commit != 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc':
    raise SystemExit(f'Unexpected Lean commit: {commit}')
mathlib_lib = args.mathlib / '.lake/build/lib/lean'
stacks_lib = args.stacks / '.lake/build/lib/lean'
required = [
    mathlib_lib / 'Mathlib/CategoryTheory/Monoidal/Cartesian/Grp.olean',
    mathlib_lib / 'Mathlib/CategoryTheory/Monoidal/Cartesian/Over.olean',
    stacks_lib / 'StacksFrontier/AlgebraicGeometry/Variety/Frobenius/Twist.olean',
]
for file in required:
    if not file.is_file():
        raise SystemExit(f'Required prebuilt artifact is absent: {file}')
    with file.open('rb') as stream:
        header = stream.read(96)
    if b'4.35.0' not in header or commit.encode() not in header:
        raise SystemExit(f'Incompatible cached artifact header: {file}')
source = args.source.resolve()
package_root = source.parent
paths = [mathlib_lib, stacks_lib, *args.dependency_lib, source.parent]
if args.source_root is not None:
    package_root = args.source_root.resolve()
    if not package_root.is_dir():
        raise SystemExit('Explicit source root is not an existing directory')
    try:
        source.relative_to(package_root)
    except ValueError:
        raise SystemExit('Proof source is outside the explicit package root')
    if package_root != source.parent:
        paths.append(package_root)
if any(not path.is_dir() for path in paths):
    raise SystemExit('An explicitly supplied cached library directory is absent')
env = dict(os.environ, LEAN_PATH=os.pathsep.join(str(path.resolve()) for path in paths),
           LEAN_NUM_THREADS='1', LEAN_ABORT_ON_PANIC='1')
# Direct Lean never resolves dependencies, fetches caches, or invokes Lake builds.
print(f'Verified Lean {commit} and the three prebuilt import artifacts.', flush=True)
command = [str(lean)]
if args.olean is not None:
    output = args.olean.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    command += ['-o', str(output)]
if args.source_root is not None:
    command.append('--root=' + str(package_root))
command.append(str(source))
raise SystemExit(subprocess.run(command, cwd=package_root, env=env).returncode)
