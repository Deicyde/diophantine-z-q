#!/usr/bin/env python3
"""Check revision 3's narrow delta and bindings; not mathematical validity."""
from pathlib import Path
import argparse
import copy
import hashlib
import importlib.util
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REVIEW = ROOT / 'research/quartic214-revision3-review/REVIEW.json'

def require(value, message):
    if not value:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def load(path):
    return json.loads(path.read_bytes())

def check_pin(record):
    path = Path(record['path'])
    require(not path.is_absolute() and '..' not in path.parts, 'unsafe path')
    raw = (ROOT / path).read_bytes()
    require(sha(raw) == record['sha256'], 'stale binding: ' + path.as_posix())
    if 'bytes' in record:
        require(len(raw) == record['bytes'], 'stale size')

def check_delta(overlay, current):
    check_pin(overlay['predecessor_tex'])
    before = (ROOT / overlay['predecessor_tex']['path']).read_bytes().decode().splitlines()
    after = current.decode().splitlines()
    require(len(before) == len(after), 'changed line count')
    expected = copy.copy(before)
    for fix in overlay['notation']:
        require(fix['id'] in {'CURRENT-RECEIVING-L3', 'CURRENT-RECEIVING-T0'}, 'unexpected repair')
        index = fix['tex_line'] - 1
        require(expected[index].count(fix['old_tex']) == 1, 'wrong original notation')
        expected[index] = expected[index].replace(fix['old_tex'], fix['new_tex'])
    require({f['id'] for f in overlay['notation']} == {'CURRENT-RECEIVING-L3', 'CURRENT-RECEIVING-T0'}, 'missing repair')
    edition = overlay['edition']
    require(before.count(edition['old']) == 1, 'wrong edition')
    expected[before.index(edition['old'])] = edition['new']
    require(after == expected, 'unreviewed manuscript difference')
    require('L3L_{4}' not in after[2241] and 'L_{3}L_{4}' in after[2241], 'missing Lucas index')
    require('Tt0' not in after[2257] and 'Tt_{0}' in after[2257], 'missing scale index')

def check_inventory(record):
    check_pin(record['historical_source'])
    original = load(ROOT / record['historical_source']['path'])['uses'][0]
    require(original['id'] == record['id'] == 'U01', 'wrong inventory use')
    require(original['required_assertion'] == record['historical_text'], 'changed original assertion')
    require(record['current_text'] == record['historical_text'].replace('214 rows encode', '188 rows in 214 coordinates encode'), 'wrong current assertion')
    require(record['current_text'].startswith('188 rows in 214 coordinates encode'), 'missing row correction')

def check_review(review):
    require(review['schema'] == 'quartic214-revision3-independent-review/v1', 'wrong review schema')
    require(review['decision'] == 'accepted-at-stated-scope', 'unaccepted repair')
    require(review['reviewer'] not in review['authors'] and '/root' in review['authors'], 'self approval')
    require(review['controller_acceptance'] is False, 'unsupported App acceptance')
    require(set(review['resolved_findings']) == {'CURRENT-RECEIVING-L3', 'CURRENT-RECEIVING-T0', 'CURRENT-RECEIVING-U01'}, 'open receiving finding')
    check_pin(review['manifest'])
    require(review['manifest']['path'] == 'research/quartic214-manuscript-revision3/MANIFEST.json', 'wrong manifest')
    require(bool(review['scope']) and bool(review['limitations']), 'missing review scope')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reviewed-artifacts', action='store_true')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    overlay = load(HERE / 'CORRECTIONS.json')
    raw = (HERE / 'quartic214.tex').read_bytes()
    check_delta(overlay, raw)
    check_inventory(overlay['inventory'])
    spec = importlib.util.spec_from_file_location('revision3_assembler', HERE / 'assemble.py')
    assembler = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(assembler)
    for name, expected in assembler.assemble().items():
        require((HERE / name).read_bytes() == expected, 'stale generated artifact')
    build = load(HERE / 'BUILD.json')
    require(build['source_files']['research/quartic214-manuscript-revision3/quartic214.tex'] == sha(raw), 'stale PDF source')
    check_pin(build['pdf'])
    require(build['limits']['parallel_tex_processes'] == 1 and build['limits']['child_address_space_bytes'] <= 1024**3 and not build['limits']['shell_escape'], 'build limits changed')
    manifest = load(HERE / 'MANIFEST.json')
    actual = {p.relative_to(ROOT).as_posix() for p in HERE.rglob('*') if p.is_file() and p.name != 'MANIFEST.json'}
    require(actual == {p['path'] for p in manifest['files']}, 'manifest file mismatch')
    for record in manifest['files'] + manifest['external_bindings']:
        check_pin(record)
    if args.reviewed_artifacts:
        check_review(load(REVIEW))
    controls = []
    if args.self_test:
        def reject(name, expected, callback):
            try:
                callback()
            except ValueError as exc:
                require(str(exc) == expected, 'wrong rejection: ' + name)
                controls.append(name)
            else:
                raise ValueError('missed rejection: ' + name)
        reject('lost Lucas index', 'unreviewed manuscript difference', lambda: check_delta(overlay, raw.replace(b'L_{3}L_{4}', b'L3L_{4}', 1)))
        reject('lost scale index', 'unreviewed manuscript difference', lambda: check_delta(overlay, raw.replace(b'Tt_{0}', b'Tt0', 1)))
        reject('unrelated edit', 'unreviewed manuscript difference', lambda: check_delta(overlay, raw.replace(b'214', b'215', 1)))
        altered = copy.deepcopy(overlay['inventory']); altered['current_text'] = altered['historical_text']
        reject('uncorrected row count', 'wrong current assertion', lambda: check_inventory(altered))
        if args.reviewed_artifacts:
            review = load(REVIEW)
            changed = copy.deepcopy(review); changed['manifest']['sha256'] = '0' * 64
            reject('stale independent review', 'stale binding: research/quartic214-manuscript-revision3/MANIFEST.json', lambda: check_review(changed))
            changed = copy.deepcopy(review); changed['reviewer'] = '/root'
            reject('self approval', 'self approval', lambda: check_review(changed))
    print(json.dumps({'status': 'PASS', 'independent_receipt_checked': args.reviewed_artifacts, 'negative_controls': controls, 'scope': 'Finite delta and binding checks only; native model authentication and App acceptance remain separate.'}))

if __name__ == '__main__':
    main()
