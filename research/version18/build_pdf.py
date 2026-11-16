#!/usr/bin/env python3
"""Build a declared TeX project serially with pdfLaTeX and record its real inputs.

Python 3.10+, Windows MiKTeX or Linux pdfLaTeX, and Poppler pdfinfo/pdftotext.
No network installer, shell command, platform-only import, or manuscript edit.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tempfile
import time

AUXILIARY = {'.aux', '.toc', '.out', '.lof', '.lot', '.nav', '.snm', '.bbl', '.bcf', '.run.xml'}


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(65536), b''):
            digest.update(block)
    return digest.hexdigest()


def repository_path(root, name):
    parts = name.split('/')
    reserved = {'con', 'prn', 'aux', 'nul'} | {f'{p}{n}' for p in ('com', 'lpt') for n in range(1, 10)}
    if (not name or PurePosixPath(name).is_absolute() or any(ord(c) < 32 for c in name)
            or any(c in name for c in '\\:<>"|?*')
            or any(p in ('', '.', '..') or p != p.rstrip(' .') or p.split('.')[0].lower() in reserved for p in parts)):
        raise ValueError('Expected a portable repository-relative file path: ' + name)
    result = (root / name).resolve()
    if not result.is_relative_to(root):
        raise ValueError('Path escapes repository: ' + name)
    return result


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


def tool(name, flag):
    executable = shutil.which(name)
    if not executable:
        raise ValueError('Required tool is missing: ' + name)
    result = subprocess.run([executable, flag], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            encoding='utf-8', errors='replace', timeout=30, check=True)
    lines = result.stdout.splitlines()
    if not lines:
        raise ValueError('Tool returned no version: ' + name)
    return executable, {'version': lines[0], 'executable_sha256': sha(Path(executable))}


def diagnostics(text):
    lines = text.splitlines()
    return {
        'tex_error_lines': [line for line in lines if re.search(
            r'^!|^.+\.(?:tex|sty|cls|def|cfg):\d+:|Emergency stop|Fatal error occurred', line)],
        'unresolved_reference_lines': [line for line in lines if re.search(
            r'(?:Reference|Citation).*\bundefined\b|undefined references|undefined citations|'
            r'multiply defined|destination with the same identifier|duplicate (?:label|destination)', line, re.I)],
        'rerun_lines': [line for line in lines if re.search(
            r'Rerun to get|Label\(s\) may have changed|rerunfilecheck Warning|'
            r'Please (?:\(re\))?run (?:LaTeX|Biber)', line, re.I)],
        'layout_lines': [line for line in lines if 'Overfull ' in line or 'Underfull ' in line],
    }


def auxiliary_state(output):
    return {p.relative_to(output).as_posix(): sha(p) for p in sorted(output.rglob('*'))
            if p.is_file() and (p.suffix in AUXILIARY or p.name.endswith('.run.xml'))}


def consumed_inputs(fls, project, output, working, declared, repository_root):
    """Hash recorder-listed source/system files; generated files are tracked separately."""
    entries, generated, pwd = {}, [], working
    for line in fls.read_text(encoding='utf-8', errors='strict').splitlines():
        if line.startswith('PWD '):
            pwd = Path(line[4:].strip('"'))
        if not line.startswith('INPUT '):
            continue
        path = Path(line[6:].strip('"'))
        path = (path if path.is_absolute() else pwd / path).resolve()
        if not path.is_file():
            raise ValueError('Recorder input cannot be hashed: ' + path.name)
        if path.is_relative_to(output):
            generated.append(path.relative_to(output).as_posix())
            continue
        if path.is_relative_to(project):
            name = path.relative_to(project).as_posix()
            if name not in declared:
                raise ValueError('Undeclared project input: ' + name)
            logical = 'repository/' + name
        elif path.is_relative_to(repository_root):
            raise ValueError('Repository input was not in the staged project: ' + path.relative_to(repository_root).as_posix())
        else:
            logical = 'system-input/' + path.name + '/' + sha(path)
        entry = {'name': logical, 'sha256': sha(path), 'bytes': path.stat().st_size}
        if path.suffix.lower() in {'.sty', '.cls', '.def'}:
            match = re.search(r'\\Provides(?:Package|Class|File)\s*\{[^}]+\}\s*\[([^\]]+)\]',
                              path.read_text(encoding='utf-8', errors='replace'))
            if match:
                entry['declared_version'] = ' '.join(match[1].split())
        entries[logical] = entry
    return [entries[k] for k in sorted(entries)], sorted(set(generated))


def publish_file(source, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=target.parent, delete=False) as stream:
        temporary = Path(stream.name)
        with source.open('rb') as incoming:
            shutil.copyfileobj(incoming, stream)
    try:
        os.replace(temporary, target)
    finally:
        temporary.unlink(missing_ok=True)


def build(args):
    root = args.repo.resolve()
    source = repository_path(root, args.source)
    pdf_target = repository_path(root, args.pdf)
    record_target = repository_path(root, args.record)
    output_root = repository_path(root, args.build_dir)
    names = [args.source] + args.input
    if len(set(n.casefold() for n in names)) != len(names):
        raise ValueError('Duplicate declared input')
    declared = {name: repository_path(root, name) for name in names}
    if any(not path.is_file() for path in declared.values()):
        raise ValueError('Every declared source/input must exist')
    if source.suffix != '.tex' or pdf_target.suffix != '.pdf' or record_target.suffix != '.json':
        raise ValueError('Source, PDF and build record must have .tex, .pdf and .json suffixes')
    paths = list(declared.values()) + [pdf_target, record_target]
    if len(set(paths)) != len(paths) or any(p.is_relative_to(output_root) for p in paths):
        raise ValueError('Build directory or release outputs overlap the declared project')
    if not args.replace and (pdf_target.exists() or record_target.exists()):
        raise ValueError('Release output exists; use --replace only when replacement is intended')
    if args.version < 1 or args.max_passes < 2 or args.timeout < 1 or args.min_pages < 1:
        raise ValueError('Version/pages/timeout must be positive; at least two serial passes are required')
    source_date = dt.datetime.fromtimestamp(args.source_date_epoch, dt.timezone.utc).isoformat()
    output_root.mkdir(parents=True, exist_ok=False)  # A fresh directory also prevents concurrent reuse.
    project, output = output_root / 'project', output_root / 'tex'
    project.mkdir()
    output.mkdir()
    source_hashes = {name: sha(path) for name, path in declared.items()}
    record = {'schema': f'quartic_v{args.version}-pdf-build/v1', 'manuscript_version': args.version,
              'status': 'building', 'source': args.source, 'source_sha256': source_hashes[args.source],
              'source_files': source_hashes, 'source_date': source_date,
              'source_date_epoch': args.source_date_epoch,
              'builder_sha256': sha(Path(__file__)), 'python': sys.version.split()[0],
              'platform': sys.platform, 'passes': [], 'tex_errors': None, 'unresolved_references': None,
              'limits': {'parallel_tex_processes': 1, 'wall_seconds_per_pass': args.timeout,
                         'shell_escape': False, 'memory_limit_enforced': False},
              'scope': 'Recorded build inputs, diagnostics and source/PDF identity only; '
                       'mathematical completeness and independent source/PDF review remain separate.'}
    started = time.monotonic()
    try:
        for name, path in declared.items():
            staged = project / name
            staged.parent.mkdir(parents=True, exist_ok=True)
            staged.write_bytes(path.read_bytes())
            os.utime(staged, (args.source_date_epoch, args.source_date_epoch))
            if sha(staged) != source_hashes[name]:
                raise ValueError('Source changed while staging: ' + name)
        tools = {name: tool(name, '--version' if name == 'pdflatex' else '-v')
                 for name in ('pdflatex', 'pdfinfo', 'pdftotext')}
        record['tools'] = {name: identity for name, (_, identity) in tools.items()}
        record['engine'] = tools['pdflatex'][1]['version']
        record['bundle'] = (record['engine'] + '; installed distribution, no monolithic bundle pin; '
                            'exact recorder-listed non-generated inputs are hashed in tex_inputs')
        miktex = 'MiKTeX' in record['engine']
        working = (project / args.source).parent
        job = source.stem
        if not re.fullmatch(r'[A-Za-z0-9_-]+', job):
            raise ValueError('Source basename must use letters, digits, underscore or hyphen')
        flags = (['-disable-write18', '-disable-installer', '-dont-parse-first-line',
                  '-job-time=./' + source.name] if miktex else ['-no-shell-escape', '-no-parse-first-line'])
        command = ['pdflatex', *flags, '-interaction=nonstopmode', '-halt-on-error', '-file-line-error',
                   '-recorder', '-jobname=' + job,
                   '-output-directory=' + os.path.relpath(output, working).replace('\\', '/'), './' + source.name]
        record['command'] = command
        record['command_working_directory'] = working.relative_to(root).as_posix()
        record['build_directory'] = args.build_dir
        record['environment'] = {'SOURCE_DATE_EPOCH': str(args.source_date_epoch), 'FORCE_SOURCE_DATE': '1', 'TZ': 'UTC'}
        env = {**os.environ, **record['environment']}
        # The staged declared files and installed TeX distribution determine resolution.
        removed = [key for key in ('TEXINPUTS', 'BIBINPUTS', 'BSTINPUTS', 'TEXMFOUTPUT') if key in env]
        for key in removed:
            del env[key]
        record['removed_search_environment_variables'] = removed
        previous, inputs, stable = None, {}, False
        for number in range(1, args.max_passes + 1):
            before = auxiliary_state(output)
            console_path = output_root / f'pass-{number:02d}.console.log'
            with console_path.open('wb') as console:
                result = subprocess.run([tools['pdflatex'][0], *command[1:]], cwd=working, env=env,
                                        stdout=console, stderr=subprocess.STDOUT, timeout=args.timeout)
            log, fls = output / (job + '.log'), output / (job + '.fls')
            text = log.read_text(encoding='utf-8', errors='replace') if log.is_file() else ''
            diagnostic = diagnostics(text)
            after = auxiliary_state(output)
            pass_record = {'pass': number, 'returncode': result.returncode,
                           'console_log': console_path.relative_to(output_root).as_posix(),
                           'auxiliary_before': before, 'auxiliary_after': after, **diagnostic}
            record['passes'].append(pass_record)
            for file in (log, fls):
                if file.is_file():
                    evidence = output_root / f'pass-{number:02d}{file.suffix}'
                    shutil.copyfile(file, evidence)
                    pass_record[file.suffix[1:] + '_evidence'] = {
                        'path': evidence.relative_to(root).as_posix(), 'sha256': sha(evidence)}
            record['tex_errors'] = len(diagnostic['tex_error_lines']) if log.is_file() else None
            record['unresolved_references'] = len(diagnostic['unresolved_reference_lines']) if log.is_file() else None
            if result.returncode or not log.is_file():
                raise ValueError('pdfLaTeX failed; see the recorded pass log and return code')
            observed, generated = consumed_inputs(fls, project, output, working, declared, root)
            pass_record['generated_inputs'] = generated
            for entry in observed:
                if entry['name'] in inputs and inputs[entry['name']] != entry:
                    raise ValueError('Consumed source/system input changed between passes')
                inputs[entry['name']] = entry
            if previous == after and not diagnostic['rerun_lines']:
                stable = True
                break
            previous = after
        record['serial_passes'] = len(record['passes'])
        record['tex_inputs'] = [inputs[key] for key in sorted(inputs)]
        record['input_hash_observation'] = ('Non-generated recorder inputs hashed after each pass; declared '
            'project copies and original sources verified unchanged. Generated input names and before/after '
            'auxiliary hashes are recorded per pass, not misrepresented as immutable source inputs.')
        if not stable or record['tex_errors'] != 0 or record['unresolved_references'] != 0:
            raise ValueError('References did not stabilize without TeX errors or unresolved/duplicate references')
        for name, path in declared.items():
            if sha(path) != source_hashes[name] or sha(project / name) != source_hashes[name]:
                raise ValueError('Declared source changed during build: ' + name)
        consumed_project = {entry['name'][11:] for entry in record['tex_inputs'] if entry['name'].startswith('repository/')}
        if args.source not in consumed_project:
            raise ValueError('Recorder did not identify the declared entry point')
        record['unused_declared_inputs'] = sorted(set(declared) - consumed_project)
        pdf = output / (job + '.pdf')
        if not pdf.is_file() or not pdf.read_bytes().startswith(b'%PDF-'):
            raise ValueError('pdfLaTeX did not produce a PDF')
        info = subprocess.run([tools['pdfinfo'][0], str(pdf)], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              encoding='utf-8', errors='replace', timeout=60, check=True).stdout
        (output_root / 'pdfinfo.txt').write_text(info, encoding='utf-8')
        fields = dict(re.findall(r'^([^:\n]+):\s*(.*)$', info, re.M))
        pages = int(fields.get('Pages', '0'))
        extracted = output_root / (job + '.txt')
        subprocess.run([tools['pdftotext'][0], '-enc', 'UTF-8', str(pdf), str(extracted)],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60, check=True)
        pdf_text = extracted.read_text(encoding='utf-8')
        if pages < args.min_pages or any(phrase not in pdf_text for phrase in args.expect_text):
            raise ValueError('PDF page/text expectations failed')
        record.update(status='success', pdf=args.pdf, pdf_sha256=sha(pdf), pdf_bytes=pdf.stat().st_size,
                      pdf_metadata=fields, pdf_text_sha256=sha(extracted), auxiliary_stable=True,
                      pdf_expectations={'minimum_pages': args.min_pages, 'text': args.expect_text},
                      elapsed_seconds=round(time.monotonic() - started, 3))
        # Only a successful record can be mapped to the public release output paths.
        release_record = output_root / 'BUILD.json'
        write_json(release_record, record)
        if not args.replace and (pdf_target.exists() or record_target.exists()):
            raise ValueError('Release target appeared during build; refusing replacement')
        publish_file(pdf, pdf_target)
        publish_file(release_record, record_target)
        return record
    except Exception as error:
        record.update(schema=f'quartic_v{args.version}-pdf-build-attempt/v1', status='failed',
                      failure_type=type(error).__name__, failure=str(error),
                      elapsed_seconds=round(time.monotonic() - started, 3))
        record.pop('pdf', None)  # A failed attempt must not masquerade as a release mapping.
        write_json(output_root / 'BUILD-attempt.json', record)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path.cwd())
    parser.add_argument('--version', type=int, default=18)
    parser.add_argument('--source', default='manuscripts/quartic_v18.tex')
    parser.add_argument('--input', action='append', default=[], help='Required local input, repository-relative; repeat as needed')
    parser.add_argument('--pdf', default='manuscripts/quartic_v18.pdf')
    parser.add_argument('--record', default='research/version18/BUILD.json')
    parser.add_argument('--build-dir', default='build/paper/release-v18', help='New, repository-relative evidence directory')
    parser.add_argument('--source-date-epoch', type=int, required=True)
    parser.add_argument('--max-passes', type=int, default=6)
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--min-pages', type=int, default=1)
    parser.add_argument('--expect-text', action='append', default=[])
    parser.add_argument('--replace', action='store_true', help='Permit replacing the explicitly selected PDF/build record')
    args = parser.parse_args()
    try:
        result = build(args)
    except Exception as error:
        print(type(error).__name__ + ': ' + str(error), file=sys.stderr)
        return 1
    print(json.dumps({key: result[key] for key in ('status', 'source', 'pdf', 'pdf_sha256', 'serial_passes', 'elapsed_seconds')}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
