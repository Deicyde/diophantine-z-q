"""Write the exact decimal specialization of the already normalized core SOS.

No compiler is imported, no row is re-normalized, and no coordinate is added.
The independent final table auditor expands these specialized residuals again.
"""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import argparse, hashlib, json, os, re, sys, tempfile

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent,
                                     prefix='.' + path.name + '.', delete=False) as f:
        temporary = Path(f.name)
        json.dump(value, f, indent=2)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
    os.replace(temporary, path)


def evaluate(entries, parameter):
    out = defaultdict(Fraction)
    for t in entries:
        power = t.get('sPower', 0)
        monomial = tuple(t['monomial'])
        assert isinstance(power, int) and power >= 0
        assert monomial == tuple(sorted(monomial))
        out[monomial] += Fraction(t['coefficient']) * parameter ** power
    assert all(a.denominator == 1 for a in out.values())
    return [{'sPower': 0, 'monomial': list(m), 'coefficient': str(a.numerator)}
            for m, a in sorted(out.items()) if a]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('directory', type=Path)
    ap.add_argument('--expected-exponent', type=int, required=True)
    args = ap.parse_args()
    d = args.directory.resolve()
    source = d / 'final/polynomial/compiled-ir.json'
    table_source = d / 'final/polynomial/polynomial.json'
    ir, table = read(source), read(table_source)
    expected = {'name': 'S', 'value': f'3^{args.expected_exponent}', 'coordinate': False}
    assert ir['fixedParameter'] == expected
    assert table['fixedParameter'] == 'S = ' + expected['value']
    assert 1 <= args.expected_exponent <= 100000
    parameter = 3 ** args.expected_exponent
    n = len(ir['coordinates'])
    destination = d / f'ordinary{n}'
    assert not (destination / 'lifted-ir.json').exists()
    provenance = {'method': 'Exact evaluation of the already normalized residuals; no normalization, elimination, or extra coordinates.',
                  'fixedParameter': expected, 'expectedExponent': args.expected_exponent,
                  'sourceIrSha256': digest(source), 'sourcePolynomialSha256': digest(table_source)}
    specialized = {'schema': 'brox-quadratic-ir-v1', 'fixedParameter': expected,
                   'coordinates': ir['coordinates'],
                   'residuals': [{**{k: v for k, v in row.items() if k != 'terms'},
                                  'terms': evaluate(row['terms'], parameter)}
                                 for row in ir['residuals']],
                   'counts': {'coordinates': n, 'residuals': len(ir['residuals'])},
                   'directSpecialization': provenance}
    decimal = {**table, 'terms': evaluate(table['terms'], parameter),
               'construction': 'Exact decimal specialization of the normalized core SOS; no residual renormalization.',
               'directSpecialization': provenance}
    assert decimal['sosMultiplier'] == '1'
    coefficients = [abs(int(t['coefficient'])) for t in decimal['terms']]
    report = {'status': 'PASS', **provenance,
              'coordinates': n, 'residuals': len(specialized['residuals']),
              'monomials': len(decimal['terms']), 'degree': max(map(lambda t: len(t['monomial']), decimal['terms'])),
              'fixedParameterDecimalDigits': len(str(parameter)),
              'maximumCoefficientBits': max(coefficients).bit_length(),
              'maximumCoefficientDigits': len(str(max(coefficients))),
              'specializerSha256': digest(Path(__file__).resolve())}
    write(destination / 'specialized-ir.json', specialized)
    write(destination / 'polynomial/compiled-ir.json', specialized)
    write(destination / 'polynomial/polynomial.json', decimal)
    mapping_source = d / 'final/polynomial/coordinate-map.json'
    write(destination / 'polynomial/coordinate-map.json', read(mapping_source))
    report['specializedIrSha256'] = digest(destination / 'specialized-ir.json')
    report['specializedPolynomialSha256'] = digest(destination / 'polynomial/polynomial.json')
    write(destination / 'specialization-report.json', report)
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
