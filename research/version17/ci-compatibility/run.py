"""Run exact historical checks against their frozen publication metadata."""
import argparse
from contextlib import contextmanager
import hashlib
import json
from pathlib import Path
import runpy
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SELECTOR = 'docs/current-manuscript.json'
OLD_SELECTOR = 'research/version17/historical-continuation/historical/current-manuscript.json'
MODES = {
    'version16-check': ('research/version16/check.py', (), {
        'CITATION.bib': 'historical/CITATION.bib',
        'manuscripts/README.md': 'historical/manuscripts-README.md',
        '.github/workflows/version16-checks.yml': 'historical/version16-checks.yml',
    }),
    'main-assemble': ('research/quartic214-manuscript/assemble.py', ('--check',), {SELECTOR: OLD_SELECTOR}),
    'main-corrections': ('research/quartic214-manuscript/check_source_corrections.py', (), {SELECTOR: OLD_SELECTOR}),
    'revision2-check': ('research/quartic214-manuscript-revision2/check_records.py', ('--self-test', '--reviewed-artifacts'), {
        SELECTOR: OLD_SELECTOR,
        '.github/workflows/quartic214-manuscript-revision2.yml': 'historical/quartic214-manuscript-revision2.yml',
    }),
}


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def archive_path(name):
    return ROOT / name if name == OLD_SELECTOR else HERE / name


def validate_mode(name, command, arguments, mapping):
    require(name in MODES, 'undeclared-mode')
    require((command, tuple(arguments), mapping) == MODES[name], 'undeclared-command-or-substitution')


def validate_bindings():
    record = json.loads((HERE / 'BINDINGS.json').read_bytes())
    require(record['schema'] == 'v17-historical-ci-bindings/v1', 'incorrect-bindings-schema')
    required = {c for c, _, _ in MODES.values()} | {
        'research/version17/ci-compatibility/run.py', 'research/version17/ci-compatibility/README.md',
        '.github/workflows/version16-checks.yml', '.github/workflows/quartic214-manuscript.yml',
        '.github/workflows/quartic214-manuscript-revision2.yml',
        'research/version16/MANIFEST.json', 'research/quartic214-manuscript-revision2/MANIFEST.json',
        'research/quartic214-manuscript-revision2/SOURCE_SPANS.json',
    }
    for _, _, mapping in MODES.values():
        required.update(mapping)
        required.update(archive_path(p).relative_to(ROOT).as_posix() for p in mapping.values())
    entries = record['files']
    require(len(entries) == len(required) and {p['path'] for p in entries} == required, 'incomplete-bindings')
    for item in entries:
        name = item['path']
        require(not Path(name).is_absolute() and '..' not in Path(name).parts, 'unsafe-binding')
        raw = (ROOT / name).read_bytes()
        require(digest(raw) == item['sha256'] and len(raw) == item['bytes'], 'changed-bound-file:' + name)
    return record


@contextmanager
def historical_reads(name, command, arguments, mapping):
    validate_mode(name, command, arguments, mapping)
    reads = {ROOT / path: archive_path(archive).read_bytes() for path, archive in mapping.items()}
    original_bytes, original_text = Path.read_bytes, Path.read_text
    def read_bytes(path):
        return reads[path] if path in reads else original_bytes(path)
    def read_text(path, encoding=None, errors=None, *args, **kwargs):
        if path not in reads:
            return original_text(path, encoding, errors, *args, **kwargs)
        # All allowed historical JSON/metadata is UTF-8. Preserve normal text
        # reading's universal-newline behavior, while raw reads stay byte exact.
        return reads[path].decode(encoding or 'utf-8', errors or 'strict').replace('\r\n', '\n').replace('\r', '\n')
    Path.read_bytes, Path.read_text = read_bytes, read_text
    try:
        yield
    finally:
        Path.read_bytes, Path.read_text = original_bytes, original_text


def controls():
    rejected = []
    def reject(label, fn):
        try:
            fn()
        except ValueError:
            rejected.append(label)
        else:
            raise ValueError('unrejected-control:' + label)
    command, arguments, mapping = MODES['main-assemble']
    reject('arbitrary-command', lambda: validate_mode('main-assemble', 'scripts/other.py', arguments, mapping))
    reject('write-mode', lambda: validate_mode('main-assemble', command, (), mapping))
    reject('arbitrary-proof-substitution', lambda: validate_mode('main-assemble', command, arguments, {**mapping, 'manuscripts/quartic_v16.tex': OLD_SELECTOR}))
    reject('missing-substitution', lambda: validate_mode('main-assemble', command, arguments, {}))
    reject('unknown-mode', lambda: validate_mode('arbitrary', command, arguments, mapping))
    proof = ROOT / 'manuscripts/quartic_v16.tex'
    raw = proof.read_bytes()
    selector = (ROOT / SELECTOR).read_bytes()
    with historical_reads('main-assemble', command, arguments, mapping):
        require(proof.read_bytes() == raw, 'proof-read-redirected')
        require((ROOT / SELECTOR).read_bytes() == (ROOT / OLD_SELECTOR).read_bytes(), 'historical-selector-not-used')
    require((ROOT / SELECTOR).read_bytes() == selector, 'current-selector-not-restored')
    return rejected + ['proof-bytes-live', 'current-selector-restored']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=sorted(MODES))
    args = parser.parse_args()
    validate_bindings()
    # Validate the actual current publication before installing any historical
    # reads. The existing Paper build job separately enforces publication order.
    sys.path.insert(0, str(ROOT / 'scripts'))
    import check_current_manuscript
    check_current_manuscript.validate(ROOT)
    checks = controls()
    command, arguments, mapping = MODES[args.mode]
    saved = sys.argv
    try:
        sys.argv = [str(ROOT / command), *arguments]
        with historical_reads(args.mode, command, arguments, mapping):
            runpy.run_path(str(ROOT / command), run_name='__main__')
    finally:
        sys.argv = saved
    print(json.dumps({'status': 'PASS', 'mode': args.mode, 'historical_reads': sorted(mapping),
                      'controls': checks, 'scope': 'Unchanged historical command and all its checks; actual current selector separately validated.',
                      'mathematical_acceptance_renewed': False, 'controller_acceptance': False}, indent=2))


if __name__ == '__main__':
    main()
