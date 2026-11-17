"""Compile the core and unique scaled-squaring constant-chain lifts.

Each --chain a,b,... specifies x0=3^a and xi=3^b*x(i-1)^2.
Its final exponent is checked against the IR before any table is written.
"""
from pathlib import Path
import argparse
import copy
import importlib.util
import json
import sys

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def read(path):
    return json.loads(path.read_text())


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2)+'\n')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('directory', type=Path)
    ap.add_argument('--chain', action='append', required=True,
                    help='Comma-separated seed and multiplier exponents')
    args = ap.parse_args()
    directory = args.directory.resolve()
    spec = importlib.util.spec_from_file_location('compiler', directory/'tools/compile_ir.py')
    compiler = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(compiler)
    source = directory/'final/integer-candidate-ir.json'
    small = read(source)
    _, _, target_exponent = compiler.fixed_parameter(small)
    chains = []
    lengths = set()
    for text in args.chain:
        exponents = [int(s) for s in text.split(',')]
        assert exponents and all(0 <= e <= 100000 for e in exponents)
        exponent = exponents[0]
        for e in exponents[1:]:
            exponent = 2*exponent+e
        assert exponent == target_exponent, (exponents, exponent, target_exponent)
        assert len(exponents) not in lengths, 'Each table must have a distinct coordinate count'
        lengths.add(len(exponents))
        chains.append(exponents)
    for row in small['residuals']:
        for term in row['terms']:
            assert term['sPower'] in (0, 1)
            assert len(term['monomial'])+term['sPower'] <= 2
    protected = {c['name'] for c in small['coordinates'] if c.get('protected')}
    assert {'anchor.physicalA.quadratic', 'inputProduct.quadratic'} <= protected
    assert any('heightProduct.scale0' in name for name in protected)
    summary = {'symbolic': compiler.run(source, directory/'final/polynomial', True, 400)['final'],
               'lifts': {}}
    for exponents in chains:
        large = copy.deepcopy(small)
        first = max(c['id'] for c in large['coordinates'])+1
        coordinates = list(range(first, first+len(exponents)))
        for row in large['residuals']:
            for term in row['terms']:
                if term['sPower']:
                    term['monomial'] = sorted(term['monomial']+[coordinates[-1]])
                    term['sPower'] = 0
        exponent = 0
        for i, (v, e) in enumerate(zip(coordinates, exponents)):
            exponent = e if i == 0 else 2*exponent+e
            large['coordinates'].append({'id': v, 'name': f'constant.3pow{exponent}',
                                         'kind': 'base', 'protected': True})
            large['residuals'].append({
                'id': f'constant-chain-{i}', 'name': f'constant-chain-{i}',
                'terms': [{'sPower': 0, 'monomial': [v], 'coefficient': '1'},
                          {'sPower': 0, 'monomial': [] if i == 0 else [coordinates[i-1]]*2,
                           'coefficient': str(-3**e)}]})
        large['constantChain'] = {'kind': 'scaled-squaring-v1',
                                  'coefficientExponents': exponents,
                                  'targetExponent': target_exponent,
                                  'coordinates': coordinates}
        large['counts'] = {**large.get('counts', {}), 'coordinates': len(large['coordinates']),
                           'residuals': len(large['residuals'])}
        label = f'ordinary{len(large["coordinates"])}'
        destination = directory/label
        write(destination/'lifted-ir.json', large)
        summary['lifts'][label] = compiler.run(destination/'lifted-ir.json', destination/'polynomial', True, 400)['final']
    write(directory/'table-summary.json', summary)
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
