#!/usr/bin/env python3
"""Build the research manuscript serially with explicit resource ceilings."""
from __future__ import annotations
import argparse
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE_DATE_EPOCH = 1794441600  # 2026-11-12 00:00:00 UTC
MEMORY_BYTES = 1024 * 1024 * 1024
PASS_SECONDS = 180

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(65536), b''):
            h.update(block)
    return h.hexdigest()

def child_limits():
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY_BYTES, MEMORY_BYTES))
    resource.setrlimit(resource.RLIMIT_CPU, (PASS_SECONDS, PASS_SECONDS))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

def tex_dependencies(fls, temporary):
    """Bind the files TeX actually consumed without publishing local paths."""
    roots = []
    for name in ['TEXMFDIST', 'TEXMFLOCAL', 'TEXMFSYSVAR', 'TEXMFSYSCONFIG']:
        value = subprocess.check_output(['kpsewhich', '-var-value=' + name], text=True).strip()
        if value and Path(value).is_absolute():
            roots.append((name, Path(value).resolve()))
    dependencies = {}
    for line in fls.read_text(errors='strict').splitlines():
        if not line.startswith('INPUT '):
            continue
        source = Path(line[6:])
        if not source.is_absolute():
            source = ROOT / 'manuscripts' / source
        source = source.resolve()
        if not source.is_file() or source.is_relative_to(temporary):
            continue
        if source.is_relative_to(ROOT):
            logical = 'repository/' + str(source.relative_to(ROOT))
        else:
            logical = next((name + '/' + str(source.relative_to(base)) for name, base in roots if source.is_relative_to(base)), None)
            if logical is None:
                # Some distro font/configuration files live outside the TeX roots.
                # Exact hashes distinguish identically named files without exposing host paths.
                logical = 'system-input/' + source.name + '/' + sha(source)[:16]
        entry = {'name': logical, 'sha256': sha(source), 'bytes': source.stat().st_size}
        if source.suffix in {'.sty', '.cls', '.def'}:
            data = source.read_text(errors='replace')
            found = re.search(r'\\Provides(?:Package|Class|File)\s*\{[^}]+\}\s*\[([^\]]+)\]', data)
            if found:
                entry['declared_version'] = ' '.join(found.group(1).split())
        dependencies[logical] = entry
    return [dependencies[key] for key in sorted(dependencies)]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Compare a fresh PDF with the committed PDF; do not replace either artifact.')
    args = parser.parse_args()
    tex = ROOT / 'manuscripts/quartic_v17.tex'
    if not tex.is_file():
        raise SystemExit('Run the manuscript assembler first: quartic_v17.tex is missing.')
    for program in ['pdflatex', 'pdfinfo', 'pdftotext', 'kpsewhich']:
        if not shutil.which(program):
            raise SystemExit('Required program is missing: ' + program)
    lock_path = Path(tempfile.gettempdir()) / ('quartic_v17-pdf-' + hashlib.sha256(str(HERE).encode()).hexdigest()[:16] + '.lock')
    with lock_path.open('w') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise SystemExit('Another manuscript PDF build is running; builds are deliberately serial.')
        with tempfile.TemporaryDirectory(prefix='quartic_v17-pdf-') as temporary:
            out = Path(temporary)
            env = dict(os.environ, SOURCE_DATE_EPOCH=str(SOURCE_DATE_EPOCH), FORCE_SOURCE_DATE='1', TZ='UTC')
            engine = subprocess.check_output(['pdflatex', '--version'], text=True).splitlines()[0]
            tools = {name: subprocess.check_output([name, '-v'], text=True, stderr=subprocess.STDOUT).splitlines()[0] for name in ['pdfinfo', 'pdftotext']}
            previous = None
            passes = 0
            start = time.monotonic()
            for passes in range(1, 5):
                command = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error', '-file-line-error', '-recorder', '-jobname=quartic_v17', '-output-directory=' + str(out), tex.name]
                with (out / 'console.log').open('w') as console:
                    try:
                        result = subprocess.run(command, cwd=tex.parent, env=env, stdout=console, stderr=subprocess.STDOUT, timeout=PASS_SECONDS + 10, preexec_fn=child_limits)
                    except subprocess.TimeoutExpired:
                        raise SystemExit('TeX exceeded its per-pass time limit; no output was published.')
                if result.returncode:
                    text = (out / 'console.log').read_text(errors='replace')
                    debug = Path(tempfile.gettempdir()) / 'quartic_v17-build-failure.log'
                    debug.write_text(text)
                    raise SystemExit('TeX build failed under its resource ceiling:\n' + '\n'.join(text.splitlines()[-35:]))
                auxiliary = {p.suffix: sha(p) for p in out.iterdir() if p.suffix in {'.aux', '.toc', '.out'}}
                if auxiliary == previous:
                    break
                previous = auxiliary
            else:
                raise SystemExit('Cross-reference files did not stabilize in four serial passes.')
            log = (out / 'quartic_v17.log').read_text(errors='replace')
            diagnostics = [line for line in log.splitlines() if 'Overfull ' in line or 'Underfull ' in line]
            (Path(tempfile.gettempdir()) / 'quartic_v17-build-latest.log').write_text(log)
            unresolved = [line for line in log.splitlines() if re.search(r'(undefined references|undefined citations|multiply defined|destination with the same identifier)', line, re.I)]
            if unresolved:
                raise SystemExit('Unresolved or duplicate document references:\n' + '\n'.join(unresolved[:30]))
            pdf = out / 'quartic_v17.pdf'
            info = subprocess.check_output(['pdfinfo', str(pdf)], text=True)
            pages = int(re.search(r'^Pages:\s+(\d+)', info, re.M).group(1))
            subprocess.run(['pdftotext', '-enc', 'UTF-8', str(pdf), str(out / 'quartic_v17.txt')], check=True, timeout=60, preexec_fn=child_limits)
            text = (out / 'quartic_v17.txt').read_text()
            if pages < 100 or '214' not in text or '188' not in text:
                raise SystemExit('PDF does not contain the expected full manuscript.')
            inputs = [tex]
            record = {
                'schema': 'quartic_v17-pdf-build/v1',
                'source_date': datetime.datetime.fromtimestamp(SOURCE_DATE_EPOCH, datetime.timezone.utc).isoformat(),
                'engine': engine, 'serial_passes': passes,
                'tools': tools,
                'command': ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error', '-file-line-error', '-recorder', '-jobname=quartic_v17', '-output-directory=<temporary-build-directory>', 'quartic_v17.tex'],
                'command_working_directory': str(tex.parent.relative_to(ROOT)),
                'environment': {'SOURCE_DATE_EPOCH': str(SOURCE_DATE_EPOCH), 'FORCE_SOURCE_DATE': '1', 'TZ': 'UTC'},
                'tex_inputs': tex_dependencies(out / 'quartic_v17.fls', out),
                'maximum_child_rss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                'limits': {'parallel_tex_processes': 1, 'child_address_space_bytes': MEMORY_BYTES, 'cpu_seconds_per_pass': PASS_SECONDS, 'wall_seconds_per_pass': PASS_SECONDS + 10, 'shell_escape': False},
                'source_files': {str(p.relative_to(ROOT)): sha(p) for p in inputs},
                'pdf': {'path': str((ROOT / 'manuscripts/quartic_v17.pdf').relative_to(ROOT)), 'sha256': sha(pdf), 'bytes': pdf.stat().st_size, 'pages': pages},
                'pdf_text_sha256': sha(out / 'quartic_v17.txt'),
                'layout_diagnostics': diagnostics,
                'cross_references': 'auxiliary files stabilized; no unresolved-reference or duplicate-label diagnostics',
                'scope': 'Source-to-PDF build identity and finite formatting checks only; mathematical review and protected controller authorization are separate.'
            }
            record['manuscript_version'] = 17
            record['source'] = 'manuscripts/quartic_v17.tex'
            record['source_sha256'] = sha(tex)
            record['pdf_metadata'] = record['pdf']
            record['pdf_sha256'] = record['pdf']['sha256']
            record['pdf'] = 'manuscripts/quartic_v17.pdf'
            record['tex_errors'] = 0
            record['unresolved_references'] = 0
            record['bundle'] = 'TeX Live 2023 Debian; exact consumed inputs are bound in tex_inputs'
            target = ROOT / 'manuscripts/quartic_v17.pdf'
            if args.check:
                if not target.exists() or sha(target) != sha(pdf):
                    raise SystemExit('Fresh PDF differs from committed bytes; compare the recorded TeX environment before claiming reproducibility.')
            else:
                shutil.copyfile(pdf, target)
                (HERE / 'BUILD.json').write_text(json.dumps(record, indent=2) + '\n')
            print(json.dumps({'status': 'PASS', 'pages': pages, 'pdf_sha256': sha(pdf), 'serial_passes': passes, 'elapsed_seconds': round(time.monotonic() - start, 2), 'max_child_address_space_bytes': MEMORY_BYTES, 'maximum_child_rss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss, 'mode': 'check' if args.check else 'build'}))

if __name__ == '__main__':
    main()
