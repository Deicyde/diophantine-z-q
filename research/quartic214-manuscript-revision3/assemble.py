#!/usr/bin/env python3
"""Apply the three recorded receiving corrections without rewriting history."""
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def encoded(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()

def pinned(record):
    raw = (ROOT / record['path']).read_bytes()
    if digest(raw) != record['sha256']:
        raise ValueError('changed predecessor: ' + record['path'])
    return raw

def assemble():
    overlay = json.loads((HERE / 'CORRECTIONS.json').read_bytes())
    original = pinned(overlay['predecessor_tex'])
    lines = original.decode().splitlines(keepends=True)
    mapping = json.loads(pinned(overlay['predecessor_map']))
    source = pinned(overlay['arithmetic_source']).decode().splitlines()
    for fix in overlay['notation']:
        if source[fix['source_line'] - 1] != fix['original_source_line']:
            raise ValueError('changed source locus: ' + fix['id'])
        index = fix['tex_line'] - 1
        if lines[index].count(fix['old_tex']) != 1:
            raise ValueError('changed receiving locus: ' + fix['id'])
        lines[index] = lines[index].replace(fix['old_tex'], fix['new_tex'])
        spans = [s for s in mapping['spans'] if s['tex_lines'] == [index + 1, index + 1]]
        if len(spans) != 1 or spans[0]['source_lines'] != [fix['source_line']] * 2:
            raise ValueError('unexpected source span: ' + fix['id'])
        spans[0]['method'] = 'source-bound-revision3-notation-correction'
        spans[0]['revision3_correction'] = fix
    text = ''.join(lines)
    date = overlay['edition']
    if text.count(date['old']) != 1:
        raise ValueError('changed edition line')
    text = text.replace(date['old'], date['new'])
    raw = text.encode()
    mapping['schema'] = 'quartic214-receiving-revision3-source-spans/v1'
    mapping['output'] = (HERE / 'quartic214.tex').relative_to(ROOT).as_posix()
    mapping['output_sha256'] = digest(raw)
    mapping['revision3'] = overlay
    mapping['revision3']['role'] = 'author corrections; independent acceptance is separate'
    return {'quartic214.tex': raw, 'SOURCE_SPANS.json': encoded(mapping)}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name, raw in assemble().items():
        path = HERE / name
        if args.check:
            if path.read_bytes() != raw:
                raise ValueError('stale generated file: ' + name)
        else:
            path.write_bytes(raw)
    print('PASS: exact revision 3 source and map; not mathematical acceptance')

if __name__ == '__main__':
    main()
