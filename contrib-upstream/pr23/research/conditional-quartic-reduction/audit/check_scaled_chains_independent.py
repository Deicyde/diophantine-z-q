"""Independent exact reconstruction of the three selected constant-chain lifts.

This script imports no producer, compiler, or other checker. It proves the
finite polynomial identities defining the unique triangular extensions.
The accompanying uniform argument explains why those identities preserve
the projected rational zero set.
"""
import argparse
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def polynomial(terms):
    result = {}
    for term in terms:
        key = (term.get('sPower', 0), tuple(term['monomial']))
        result[key] = result.get(key, Fraction(0)) + Fraction(term['coefficient'])
    return {key: value for key, value in result.items() if value}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('directory', type=Path)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    root = args.directory.resolve()
    source_path = root/'final/integer-candidate-ir.json'
    source = read(source_path)
    expected_parameter = {'name': 'S', 'value': '3^2364', 'coordinate': False}
    assert source['fixedParameter'] == expected_parameter
    ids = [coordinate['id'] for coordinate in source['coordinates']]
    assert len(set(ids)) == len(ids) and source['coordinates'][0]['id'] == 0
    assert len(ids) == 389
    source_rows = {row['id']: polynomial(row['terms']) for row in source['residuals']}
    assert len(source_rows) == len(source['residuals'])
    assert len(source_rows) == 357
    assert all(sp in [0, 1] and sp+len(monomial) <= 2
               for row in source_rows.values() for sp, monomial in row)
    count = len(ids)
    results = []
    for exponents in [[788, 788], [338, 338, 336], [158, 158, 158, 152]]:
        path = root/('ordinary'+str(count+len(exponents)))/'lifted-ir.json'
        lifted = read(path)
        assert lifted['fixedParameter'] == expected_parameter
        first = max(ids)+1
        chain_ids = list(range(first, first+len(exponents)))
        assert lifted['coordinates'][:count] == source['coordinates']
        assert len(lifted['coordinates']) == count+len(exponents)
        assert len(lifted['residuals']) == len(source_rows)+len(exponents)
        rows = {row['id']: polynomial(row['terms']) for row in lifted['residuals']}
        assert len(rows) == len(lifted['residuals'])
        terminal = chain_ids[-1]
        for row_id, row in source_rows.items():
            substitution = {}
            for (power, monomial), coefficient in row.items():
                key = (0, tuple(sorted(monomial+(terminal,)*power)))
                substitution[key] = substitution.get(key, Fraction(0))+coefficient
            substitution = {key: value for key, value in substitution.items() if value}
            assert rows[row_id] == substitution, ('lifted base row', row_id)
        exponent = None
        for index, (coordinate_id, seed_exponent) in enumerate(zip(chain_ids, exponents)):
            exponent = seed_exponent if index == 0 else 2*exponent+seed_exponent
            expected_coordinate = {'id': coordinate_id, 'name': 'constant.3pow'+str(exponent),
                                   'kind': 'base', 'protected': True}
            assert lifted['coordinates'][count+index] == expected_coordinate
            monomial = () if index == 0 else (chain_ids[index-1],)*2
            expected_row = {(0, (coordinate_id,)): Fraction(1),
                            (0, monomial): Fraction(-3**seed_exponent)}
            assert rows['constant-chain-'+str(index)] == expected_row
        assert exponent == 2364
        assert lifted['constantChain'] == {'kind': 'scaled-squaring-v1',
                'coefficientExponents': exponents, 'targetExponent': 2364, 'coordinates': chain_ids}
        assert all(power == 0 and len(monomial) <= 2 for row in rows.values() for power, monomial in row)
        results.append({'file':path.relative_to(root).as_posix(), 'sha256':digest(path),
                'coefficientExponents':exponents, 'chainCoordinates':chain_ids,
                'terminalExponent':exponent, 'totalCoordinates':len(lifted['coordinates']),
                'residuals':len(rows), 'baseResidualsReconstructed':len(source_rows),
                'uniqueExtension':'The first row fixes x0, and every later row is monic in a fresh coordinate xi and depends only on x(i-1).',
                'quadraticAfterSubstitution':True})

    # Independently verify direct specialization on residuals, without using
    # the specializer or its implementation.
    core = read(root/'final/polynomial/compiled-ir.json')
    assert core['fixedParameter'] == expected_parameter
    specialized_path = root/('ordinary'+str(count))/'specialized-ir.json'
    specialized = read(specialized_path)
    assert specialized['fixedParameter'] == expected_parameter
    assert core['coordinates'] == specialized['coordinates']
    assert len(core['residuals']) == len(specialized['residuals'])
    assert len(core['coordinates']) == 389 and len(core['residuals']) == 357
    parameter = 3**2364
    for original, actual in zip(core['residuals'], specialized['residuals']):
        assert original['id'] == actual['id'] and original['name'] == actual['name']
        expected = {}
        for (power, monomial), coefficient in polynomial(original['terms']).items():
            key = (0, monomial)
            expected[key] = expected.get(key, Fraction(0))+coefficient*parameter**power
        expected = {key: value for key, value in expected.items() if value}
        assert expected == polynomial(actual['terms'])
        assert all(value.denominator == 1 for value in expected.values())

    report = {'status':'PASS',
        'scope':'Exact reconstruction of every precompiler base row and new constant-chain row in all three selected lifts, plus exact direct specialization of every normalized core residual. This checker imports neither producer nor compiler. Final SOS expansions and the global arithmetic implication are separate checks.',
        'builderSha256':digest(root/'builder.cjs'), 'rawIrSha256':digest(root/'raw-ir.json'),
        'sourceIrSha256':digest(source_path), 'checkerSha256':digest(Path(__file__)),
        'fixedParameter':expected_parameter, 'coreCoordinates':count,
        'coreResiduals':len(source_rows), 'chains':results,
        'directSpecialization':{'file':specialized_path.relative_to(root).as_posix(),
            'sha256':digest(specialized_path), 'coordinates':len(specialized['coordinates']),
            'residualsReconstructed':len(specialized['residuals']), 'parameterExponent':2364}}
    text=json.dumps(report,indent=2)+'\n'
    if args.report:
        args.report.write_text(text)
    print(text)


if __name__ == '__main__':
    main()
