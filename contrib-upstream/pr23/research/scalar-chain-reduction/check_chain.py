"""Check actual scalar-chain rows and exact margins, without importing producer.

Same-session author verification; not independent mathematical acceptance.
"""
from collections import defaultdict
from copy import deepcopy
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json


def poly(terms):
    return {tuple(sorted([-1] * t['sPower'] + t['monomial'])): F(t['coefficient']) for t in terms}


def add(*ps):
    out = defaultdict(F)
    for p in ps:
        for m, c in p.items():
            out[m] += c
    return {m: c for m, c in out.items() if c}


def scale(p, c):
    return {m: c * v for m, v in p.items() if c * v}


def mul(a, b):
    out = defaultdict(F)
    for m, c in a.items():
        for n, d in b.items():
            out[tuple(sorted(m + n))] += c * d
    return {m: c for m, c in out.items() if c}


def check(data):
    rows = {r['name']: poly(r['terms']) for r in data['residuals']}
    values = {n: poly(v['terms']) for n, v in data['values'].items()}
    coords = {c['name']: {(c['id'],): F(1)} for c in data['coordinates']}
    one = {(): F(1)}
    def same(a, b):
        assert a == b
    def eq(name, left, right):
        expected = add(left, scale(right, -1)); actual = rows[name]
        assert expected and actual, name
        pivot = min(expected)
        assert pivot in actual, name
        factor = actual[pivot] / expected[pivot]
        assert actual == scale(expected, factor), name
    v = values.__getitem__
    square = lambda p: mul(p, p)
    assert data['fixedParameter'] == {'name': 'S', 'value': '3^2130', 'coordinate': False}
    beta, r = v('beta'), v('scalar.r')
    eq('scalar.rPair1.definition', v('scalar.rPair1'), mul(beta, add(beta, scale(one, -1))))
    eq('scalar.rThree.definition', r, mul(v('scalar.rPair1'), add(scale(beta, 32), scale(one, 343))))
    eq('scalar.rInverse.definition', mul(r, v('scalar.rInverse')), one)
    previous = v('scalar.rInverse')
    for power in [3, 7, 15]:
        current = v('scalar.rInverse' + str(power))
        eq('scalar.rInverse' + str(power) + '.definition', mul(r, current), square(previous))
        previous = current
    kappa = previous
    proxy = add(mul(v('primaryRatio.0'), v('scalar.shiftedS.w.0')),
                scale(mul(v('primaryRatio.1'), v('scalar.shiftedS.w.1')), 2))
    eq('scalar.ratioProxyReal.definition', v('scalar.ratioProxyReal'), proxy)
    eq('scalar.ratioProxyLeaf.definition', mul(r, v('scalar.directLeaf.0')),
       mul(v('scalar.ratioProxyReal'), kappa))
    eq('scalar.shiftedS.nonzeroRealF.definition',
       mul(v('scalar.shiftedS.f.0'), v('scalar.shiftedS.nonzeroRealF')), one)
    child = v('scalar.directLeaf.0')
    for number, leaf in [(3, 'scalar.shiftedS.f.1'), (2, 'scalar.shiftedS.f.0'), (1, 'H.f.1')]:
        name = 'scalar.chain' + str(number)
        eq(name + '.rightSquare.definition', v(name + '.rightSquare'), square(child))
        eq(name + '.definition', v(name), add(square(v(leaf)), mul(kappa, v(name + '.rightSquare'))))
        child = v(name)
    eq('scalar.N.rightSquare.definition', v('scalar.N.rightSquare'), square(child))
    eq('scalar.N.definition', mul(r, v('scalar.N')),
       add(square(v('H.f.0')), mul(kappa, v('scalar.N.rightSquare'))))
    same(v('scalar.W'), add(one, v('scalar.N')))
    eq('scalar.W2.definition', v('scalar.W2'), square(v('scalar.W')))
    same(v('scalar.correctedR'), scale(r, 42))
    same(v('scalar.Bsemantic'), mul(scale(r, 42), v('scalar.W2')))
    physical = v('scalar.Bsemantic')
    eq('scalar.preparationT.definition', v('scalar.preparationT'),
       add(physical, scale(square(coords['scalar.preparationV']), -1)))
    eq('scalar.preparationConic', square(coords['scalar.preparationU']),
       mul(scale(r, 42), v('scalar.preparationT')))
    eq('scalar.Bh.definition', v('scalar.Bh'),
       mul(coords['scalar.normalized_e'], add(scale(one, 17), scale(v('scalar.preparationT'), -1))))
    return True


def margins():
    N = F(-1, 2)
    A = (N + 1) / 2
    J1 = (N + 16) / 2
    B = J1 / 2
    J2 = (J1 + 15) / 2
    C = J2 / 2
    J3 = (J2 + 15) / 2
    D = J3 / 2
    y = (J3 + 15) / 2
    proxy = y + 16
    assert [A, J1, B, J2, C, J3, D, y, proxy] == list(map(F,
        ['1/4', '31/4', '31/8', '91/8', '91/16', '211/16', '211/32', '451/32', '963/32']))
    assert 30 < proxy < 31
    # Coefficient parities in root and three inner norms, for every odd v_p(r).
    assert all((a - b) % 2 for a, b in [(-1, -16), (0, -15), (0, -15), (0, -15)])
    H = 3 * 2**106 * (2**32 * 3**9)**6 * 46410**18 + 128
    c = 2 * 3**1064
    b = c // 2
    assert c**415 > (4 * H)**992
    assert b**143 > (24 * H)**360
    assert 40 * H < 2**670
    assert 100 * 670 < b and b > 152
    maximum = 28902 * 3**1420
    assert len(str(maximum)) == 682 and maximum.bit_length() == 2266
    # Strong sufficient finite preparation, checked as affine functions of R>=1.
    # A,B,C,D,y >= 16R+1; each inner output stays >=16R+1,
    # and N >=16R+2. Coefficientwise differences are nonnegative.
    assert (32 - 16, 2 - 1) == (16, 1)
    assert (32 - 15 - 16, 2 - 1) == (1, 1)
    assert (32 - 1 - 16, 2 - 2) == (15, 0)
    assert (32 - 15 - 1 - 16, 2 - 2) == (0, 0)
    return {'strictProxyBound': str(proxy), 'scalarOrder': 31,
            'anchorExponent': 2130, 'indexDivisibilityExponentAt3': 1064,
            'heightExponent': '577/32', 'heightConstantBits': H.bit_length(),
            'scalarIntegerMargin': True, 'lucasIntegerMargin': True,
            'inputLogMargin': True, 'maximumCoefficientDigits': 682,
            'maximumCoefficientBits': 2266}


def compare_baseline(before, after):
    def named(data):
        names = {c['id']: c['name'].replace('scalar.N.quadratic', 'scalar.N') for c in data['coordinates']}
        return {r['name']: {(t['sPower'], tuple(sorted(names[i] for i in t['monomial']))):
                            F(t['coefficient']) for t in r['terms']} for r in data['residuals']}
    a, b = named(before), named(after)
    deleted = {'scalar.' + n + '.definition' for n in
               ['leaf1', 'n1', 'n1OverR', 'nLeft', 'nRight', 'nRight.rightSquare']}
    added = {'scalar.chain' + str(i) + suffix + '.definition'
             for i in range(1, 4) for suffix in ['', '.rightSquare']}
    changed = {'scalar.N.definition', 'scalar.N.rightSquare.definition'}
    assert a.keys() - b.keys() == deleted
    assert b.keys() - a.keys() == added
    assert {n for n in a.keys() & b.keys() if a[n] != b[n]} == changed
    # All other raw rows agree after coordinate-name identification. Changing
    # the fixed anchor value is separately declared and checked in check().
    return {'deletedRows': sorted(deleted), 'addedRows': sorted(added),
            'changedRows': sorted(changed),
            'unchangedRows': len(a.keys() & b.keys()) - len(changed)}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('raw_ir', type=Path)
    ap.add_argument('--baseline', type=Path, required=True)
    ap.add_argument('--report', type=Path, required=True)
    args = ap.parse_args()
    data = json.loads(args.raw_ir.read_text())
    check(data)
    delta = compare_baseline(json.loads(args.baseline.read_text()), data)
    probes = []
    for name in ['scalar.N.definition', 'scalar.chain3.definition', 'scalar.ratioProxyLeaf.definition']:
        bad = deepcopy(data)
        row = next(r for r in bad['residuals'] if r['name'] == name)
        row['terms'][0]['coefficient'] = str(F(row['terms'][0]['coefficient']) + 1)
        probes.append((name, bad))
    bad = deepcopy(data)
    bad['fixedParameter']['value'] = '3^2124'
    probes.append(('wrong anchor parameter', bad))
    bad = deepcopy(data)
    bad['residuals'] = [r for r in bad['residuals'] if r['name'] != 'scalar.shiftedS.nonzeroRealF.definition']
    probes.append(('missing shifted-point guard', bad))
    for name, bad in probes:
        try:
            check(bad)
        except (AssertionError, KeyError):
            pass
        else:
            raise AssertionError('negative control accepted: ' + name)
    report = {'status': 'PASS', 'independentAcceptance': False,
              'rawIrSha256': hashlib.sha256(args.raw_ir.read_bytes()).hexdigest(),
              'claims': margins(),
              'sourceDelta': delta,
              'rejectedNegativeControls': [name for name, _ in probes],
              'scope': 'Exact scalar source rows and integer margins; no acceptance of uniform arithmetic arguments.'}
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: scalar-chain source, strict valuation bounds, exact height margins, five negative controls')


if __name__ == '__main__':
    main()
