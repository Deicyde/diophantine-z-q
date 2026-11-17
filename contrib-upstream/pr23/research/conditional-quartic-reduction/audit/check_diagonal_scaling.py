"""Independent exact audit of the round-eight two-prime diagonal transformation.

No construction, compiler, producer, or other checker is imported.  The expected
anchor exponent and coordinate count must be supplied independently on the CLI.
The audit reconstructs every substituted quadratic row, the nonzero row divisors,
the complete sum of squares, and every coefficient of the delivered text table.
Its algebraic equivalence does not establish the inherited global arithmetic.
"""
from pathlib import Path
from fractions import Fraction
import argparse
import hashlib
import json
import math
import re
import sys

sys.set_int_max_str_digits(0)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def integer(value):
    q = Fraction(value)
    require(q.denominator == 1, 'noninteger coefficient')
    return q.numerator


def decode_integer_terms(terms, allowed_ids, maximum_degree):
    result = {}
    for term in terms:
        require(set(term) == {'monomial', 'coefficient', 'sPower'},
                'unexpected polynomial term fields')
        require(term['sPower'] == 0, 'unresolved parameter in integer output')
        monomial = tuple(term['monomial'])
        require(monomial == tuple(sorted(monomial)), 'unsorted monomial')
        require(len(monomial) <= maximum_degree, 'degree exceeds claim')
        require(set(monomial) <= allowed_ids, 'unknown coordinate in monomial')
        coefficient = integer(term['coefficient'])
        require(coefficient != 0, 'zero term in sparse output')
        require(monomial not in result, 'duplicate output monomial')
        result[monomial] = coefficient
    require(result, 'empty polynomial row')
    return result


def text_polynomial(path, count, monomials):
    result = {}
    lines = path.read_text().splitlines()
    require(len(lines) >= 3, 'text table has no header')
    require(lines[1] ==
            f'# Variables: {count}; input: x0; degree: 4; monomials: {monomials}.',
            'text-table header disagrees with independent expectations')
    require(lines[0] == '# Fully explicit integer quartic after an invertible diagonal change.',
            'wrong text-table type')
    require(lines[2] == '# Format: integer coefficient, TAB, monomial; sum all data rows.',
            'wrong text-table format declaration')
    for line in lines[3:]:
        require(line and not line.startswith('#'), 'unexpected data line')
        fields = line.split('\t')
        require(len(fields) == 2 and re.fullmatch(r'-?(?:0|[1-9][0-9]*)', fields[0]),
                'invalid integer text-table coefficient')
        coefficient = int(fields[0])
        require(coefficient != 0, 'zero text-table coefficient')
        ids = []
        last = -1
        if fields[1] != '1':
            for factor in fields[1].split('*'):
                match = re.fullmatch(r'x(0|[1-9][0-9]*)(?:\^([2-4]))?', factor)
                require(match is not None, 'invalid text-table factor')
                coordinate = int(match[1])
                multiplicity = int(match[2] or '1')
                require(last < coordinate < count, 'noncanonical text-table coordinates')
                ids.extend([coordinate] * multiplicity)
                last = coordinate
        monomial = tuple(ids)
        require(len(monomial) <= 4 and monomial not in result,
                'duplicate or excessive-degree text monomial')
        result[monomial] = coefficient
    require(len(result) == monomials, 'wrong text-table support size')
    return result


def audit(root, expected_exponent, expected_coordinates, expected_residuals=None,
          expected_monomials=None, expected_digits=None, expected_bits=None):
    source_path = root/'final/integer-candidate-ir.json'
    directory = root/'balanced'
    ir_path = directory/'integer-ir.json'
    table_path = directory/'polynomial.json'
    certificate_path = directory/'diagonal-certificate.json'
    summary_path = directory/'summary.json'
    decimal_path = root/f'quartic-{expected_coordinates}-balanced-decimal.txt'
    source, target, table, certificate, summary = map(read_json,
        [source_path, ir_path, table_path, certificate_path, summary_path])

    require(expected_exponent > 0 and expected_exponent % 6 == 0,
            'this selected scaling requires a positive exponent divisible by six')
    metadata = source['fixedParameter']
    require(metadata == {'name': 'S', 'value': f'3^{expected_exponent}', 'coordinate': False},
            'source anchor differs from independently supplied exponent')
    source_coordinates = source['coordinates']
    require(len(source_coordinates) == expected_coordinates, 'source coordinate count differs')
    by_id = {entry['id']: entry for entry in source_coordinates}
    by_name = {entry['name']: entry['id'] for entry in source_coordinates}
    require(len(by_id) == len(by_name) == expected_coordinates, 'duplicate coordinate')
    require(all(isinstance(i, int) and i >= 0 for i in by_id), 'invalid coordinate identifier')
    require(by_name.get('input') == 0 and by_id[0]['kind'] == 'input'
            and by_id[0]['protected'], 'the source input is not coordinate zero')
    ids = sorted(by_id)
    require(source_coordinates == [by_id[i] for i in ids], 'noncanonical source coordinate order')
    compact = {old: new for new, old in enumerate(ids)}

    # This list is the independently specified mathematical transformation.
    # All other old coordinates equal their corresponding new coordinates.
    unit = expected_exponent // 6
    scale_names = [
        (1, ['S.chart.h0', 'S.chart.h1', 'S.chart.x.0.quadratic',
             'S.chart.x.1.quadratic', 'scalar.shiftedS.f.0', 'scalar.shiftedS.f.1']),
        (2, ['scalar.shiftedS.rootTimesInverseRoot.0',
             'scalar.shiftedS.rootTimesInverseRoot.1']),
        (4, ['anchor.U', 'anchor.V', 'anchor.W', 'anchor.physicalA.quadratic']),
    ]
    powers = {i: 0 for i in ids}
    two_powers = {i: 0 for i in ids}
    for multiplier, names in scale_names:
        for name in names:
            require(name in by_name, 'required scaled coordinate absent: '+name)
            powers[by_name[name]] = multiplier * unit
    for name, exponent in [('S.chart.x.0.quadratic',1),
                           ('heightProduct.scale0.quadratic',-21)]:
        require(name in by_name,'required dyadically scaled coordinate absent: '+name)
        two_powers[by_name[name]]=exponent
    require(powers[0] == two_powers[0] == 0
            and sum(p != 0 for p in powers.values()) == 12
            and sum(p != 0 for p in two_powers.values()) == 2
            and sum(powers[i] != 0 or two_powers[i] != 0 for i in ids) == 13,
            'incorrect input or support for the two-prime diagonal scaling')

    require(certificate['format'] == 'diagonal-scaling-certificate-v2', 'wrong certificate type')
    require(certificate['sourceIrSha256'] == digest(source_path), 'source hash mismatch')
    require(certificate['newIrSha256'] == digest(ir_path), 'new IR hash mismatch')
    require(certificate['polynomialSha256'] == digest(table_path), 'quartic hash mismatch')
    require(certificate['anchorExponent'] == expected_exponent
            and certificate['cExponent'] == unit, 'certificate exponent mismatch')
    require(certificate['direction'] == 'old_x_i = 2^twoPower[i] * 3^threePower[i] * new_x_i',
            'wrong scaling direction')
    require(certificate['threePowers'] == {str(i): powers[i] for i in ids}
            and certificate['twoPowers'] == {str(i): two_powers[i] for i in ids},
            'certificate does not specify the expected two-prime diagonal map')
    require(target['format'] == 'diagonally-scaled-integer-quadratic-ir-v2'
            and target['coordinates'] == source_coordinates
            and target['sourceFixedParameter'] == metadata
            and target['inputCoordinate'] == 0, 'target IR interface differs')
    require(len(source['residuals']) == len(target['residuals']) == len(certificate['rows']),
            'row count mismatch')
    if expected_residuals is not None:
        require(len(source['residuals']) == expected_residuals, 'unexpected residual count')
    row_ids = [r['id'] for r in source['residuals']]
    require(len(set(row_ids)) == len(row_ids), 'duplicate source row identifier')
    require([r['id'] for r in target['residuals']] == row_ids
            and [r['id'] for r in certificate['rows']] == row_ids,
            'missing, reordered, or additional target/certificate row')

    reconstructed_rows = []
    divisors = []
    fractional_divisors = []
    span_histogram = {}
    for old_row, new_row, row_certificate in zip(source['residuals'],
                                                target['residuals'], certificate['rows']):
        require(new_row['name'] == old_row['name'], 'row name changed')
        substituted = {}
        c_powers = []
        for term in old_row['terms']:
            monomial = tuple(term['monomial'])
            require(monomial == tuple(sorted(monomial)) and len(monomial) <= 2,
                    'source residual is not quadratic')
            require(set(monomial) <= set(ids), 'unknown source coordinate')
            s_power = term['sPower']
            require(isinstance(s_power, int) and s_power >= 0, 'invalid source parameter power')
            c_powers.append(6*s_power + sum(powers[i] // unit for i in monomial))
            a = Fraction(integer(term['coefficient']) * pow(3, expected_exponent * s_power))
            for coordinate in monomial:
                a *= pow(3, powers[coordinate])
                p2=two_powers[coordinate]
                a *= Fraction(pow(2,p2),1) if p2 >= 0 else Fraction(1,pow(2,-p2))
            substituted[monomial] = substituted.get(monomial, Fraction(0)) + a
        substituted = {m: a for m, a in substituted.items() if a}
        require(substituted, 'zero source row after substitution')
        span = max(c_powers) - min(c_powers)
        require(span <= 2, 'a source row exceeds the asserted c-exponent span')
        span_histogram[span] = span_histogram.get(span, 0) + 1
        # Independent normalization: divide by the leading rational coefficient,
        # then clear the denominators of these ratios. This differs from the
        # producer's common-denominator-then-integer-gcd algorithm.
        pivot=substituted[min(substituted)]
        ratios={m:a/pivot for m,a in substituted.items()}
        ratio_denominator=math.lcm(*(a.denominator for a in ratios.values()))
        signed_divisor=pivot/ratio_denominator
        require(set(row_certificate)=={'id','divisorNumerator','divisorDenominator'},
                'unexpected rational row certificate fields')
        divisor_numerator=integer(row_certificate['divisorNumerator'])
        divisor_denominator=integer(row_certificate['divisorDenominator'])
        require(divisor_numerator!=0 and divisor_denominator>0
                and math.gcd(divisor_numerator,divisor_denominator)==1,
                'row divisor is not a nonzero canonical rational')
        require(Fraction(divisor_numerator,divisor_denominator)==signed_divisor,
                'incorrect rational row divisor')
        normalized={m:integer(a*ratio_denominator) for m,a in ratios.items()}
        require(all(Fraction(normalized[m])*signed_divisor==a for m,a in substituted.items()),
                'rational row identity failed')
        actual = decode_integer_terms(new_row['terms'], set(ids), 2)
        require(actual == normalized, 'diagonal row identity failed: '+str(old_row['id']))
        require(math.gcd(*actual.values()) == 1, 'row is not primitive')
        reconstructed_rows.append(normalized)
        divisors.append(signed_divisor)
        if signed_divisor.denominator!=1:
            fractional_divisors.append({'id':old_row['id'],'name':old_row['name'],
                                        'denominator':str(signed_divisor.denominator)})

    # Independently convolve each primitive row.  Using unordered pairs and
    # a factor of two for cross terms differs from the producer's ordered loop.
    source_sos = {}
    for row in reconstructed_rows:
        terms = sorted(row.items())
        for i, (m, a) in enumerate(terms):
            for j in range(i, len(terms)):
                n, b = terms[j]
                key = tuple(sorted(m+n))
                source_sos[key] = source_sos.get(key, 0) + a*b*(1 if i == j else 2)
    source_sos = {m: a for m, a in source_sos.items() if a}
    expected_sos = {tuple(compact[i] for i in m): a for m, a in source_sos.items()}
    require(table['format'] == 'integer-quartic-table-v1', 'wrong quartic format')
    expected_map = [{'id': compact[i], 'sourceId': i, 'name': by_id[i]['name'],
                     'oldCoordinateEqualsTwoPowerTimesThreePowerTimesNew':True,
                     'twoPower':two_powers[i],'threePower':powers[i]} for i in ids]
    require(table['coordinates'] == expected_map, 'wrong compact coordinate correspondence')
    actual_sos = decode_integer_terms(table['terms'], set(range(expected_coordinates)), 4)
    require(actual_sos == expected_sos, 'full normalized sum-of-squares expansion differs')
    require({i for m in actual_sos for i in m} == set(range(expected_coordinates)),
            'claimed coordinate is inactive')
    require(max(map(len, actual_sos)) == 4, 'quartic has wrong exact degree')
    require(actual_sos.get((0, 0, 0, 0)) == 1, 'input fourth-power coefficient is not one')
    require(math.gcd(*actual_sos.values()) == 1, 'quartic is not primitive')
    maximum = max(abs(a) for a in actual_sos.values())
    expected_maximum = 28902 * pow(3, 4*unit)
    require(maximum == expected_maximum,
            'the exact maximum differs from 28902*c^4')
    require(text_polynomial(decimal_path, expected_coordinates, len(actual_sos)) == actual_sos,
            'explicit decimal text differs from the checked quartic')

    measured = {
        'coordinates': expected_coordinates, 'residuals': len(reconstructed_rows),
        'degree': 4, 'monomials': len(actual_sos), 'integerContent': 1,
        'inputFourthPowerCoefficient': '1',
        'maximumCoefficientDigits': max(len(str(abs(a))) for a in actual_sos.values()),
        'maximumCoefficientBits': max(abs(a).bit_length() for a in actual_sos.values()),
        'scaledCoordinates': 13, 'ternaryScaledCoordinates':12,'dyadicScaledCoordinates':2,
        'anchorExponent': expected_exponent, 'cExponent': unit,
        'tableSha256': digest(decimal_path), 'tableBytes': decimal_path.stat().st_size,
        'certificateSha256': digest(certificate_path),
    }
    require(summary == measured, 'producer summary differs from independently measured values')
    for expected, field in [(expected_monomials, 'monomials'),
                            (expected_digits, 'maximumCoefficientDigits'),
                            (expected_bits, 'maximumCoefficientBits')]:
        if expected is not None:
            require(measured[field] == expected, 'unexpected '+field)
    files = [source_path, ir_path, table_path, certificate_path, summary_path, decimal_path]
    for name in ['builder.cjs', 'raw-ir.json']:
        if (root/name).exists():
            files.append(root/name)
    return {
        'status': 'PASS', 'expectedAnchorExponent': expected_exponent,
        'expectedCoordinates': expected_coordinates,
        'checkedQuadraticRows': len(reconstructed_rows),
        'checkedNonzeroRowDivisors': len(divisors),
        'rowExponentSpanHistogram': {str(k): span_histogram[k] for k in sorted(span_histogram)},
        'maximumAbsoluteCoefficientFormula': f'28902*3^{4*unit}',
        'nonintegerRowDivisors':fractional_divisors,
        'exactMaximumFormulaVerified': True,
        'fullSumOfSquaresIdentity': True, 'everyDecimalCoefficientChecked': True,
        'diagonalMapIsBijectionOverQ': True, 'inputFixed': True,
        'measured': measured,
        'fileBindings': {str(path.relative_to(root)): digest(path) for path in files},
        'checkerSha256': digest(Path(__file__).resolve()),
        'scope': 'Exact diagonal substitution at the independently specified fixed parameter, '
                 'nonzero primitive-row scaling, all normalized quadratic rows, full SOS, '
                 'coordinate compaction, and every decimal text coefficient.  The inverse '
                 'map divides each coordinate by its nonzero rational factor 2^a*3^b, '
                 'including the specified negative dyadic exponent. '
                 'Over Q a sum of rational squares vanishes exactly when every row vanishes. '
                 'This gives the same projection onto the unchanged input; inherited global '
                 'arithmetic and source-to-core compilation are separate obligations.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('construction', type=Path)
    parser.add_argument('--expected-exponent', type=int, required=True)
    parser.add_argument('--expected-coordinates', type=int, required=True)
    parser.add_argument('--expected-residuals', type=int)
    parser.add_argument('--expected-monomials', type=int)
    parser.add_argument('--expected-max-digits', type=int)
    parser.add_argument('--expected-max-bits', type=int)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    result = audit(args.construction.resolve(), args.expected_exponent,
                   args.expected_coordinates, args.expected_residuals,
                   args.expected_monomials, args.expected_max_digits,
                   args.expected_max_bits)
    args.report.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
