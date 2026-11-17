#!/usr/bin/env python3
"""Independent exact joins between already independently audited IR stages.

Uses only the standard library; imports neither a generator nor another checker.
This verifies the inherited invertible anchor translation, snapshot identity,
and primitive row normalizations. It does not prove global arithmetic.
"""
import argparse
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path


def poly(terms):
    p = {}
    for t in terms:
        m = tuple(t['monomial'])
        assert tuple(sorted(m)) == m
        k = (t.get('sPower', 0), m)
        p[k] = p.get(k, Q(0)) + Q(t['coefficient'])
    return {k: v for k, v in p.items() if v}


def add(a, b):
    r = a.copy()
    for k, v in b.items():
        r[k] = r.get(k, Q(0)) + v
    return {k: v for k, v in r.items() if v}


def mul(a, b):
    r = {}
    for (s, m), v in a.items():
        for (t, n), w in b.items():
            k = (s+t, tuple(sorted(m+n)))
            r[k] = r.get(k, Q(0)) + v*w
    return {k: v for k, v in r.items() if v}


def substitute(p, replacements):
    r = {}
    for (s, m), v in p.items():
        t = {(s, ()): v}
        for x in m:
            t = mul(t, replacements.get(x, {(0, (x,)): Q(1)}))
        r = add(r, t)
    return r


def scale(p, q):
    return {k: v*q for k, v in p.items() if v*q}


def rows(d):
    r = {x['id']: poly(x['terms']) for x in d['residuals']}
    assert len(r) == len(d['residuals'])
    return r


def proportional_rows(a, b):
    x, y = rows(a), rows(b)
    assert x.keys() == y.keys()
    factors = {}
    for i, p in x.items():
        q = y[i]
        assert p and p.keys() == q.keys()
        k = next(iter(p))
        factor = q[k]/p[k]
        assert factor and scale(p, factor) == q
        factors[str(i)] = str(factor)
    return factors


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('construction', type=Path)
    ap.add_argument('--expected-exponent', type=int, required=True)
    ap.add_argument('--report', required=True, type=Path)
    args = ap.parse_args()
    root = args.construction.resolve()
    names = ['raw-ir.json', 'raw-translated-ir.json',
             'compiled/compiled-ir.json', 'final/source-ir.json',
             'final/candidate-ir.json', 'final/integer-candidate-ir.json',
             'final/polynomial/compiled-ir.json']
    data = {n: json.loads((root/n).read_text()) for n in names}
    raw, translated = data[names[0]], data[names[1]]
    assert 1 <= args.expected_exponent <= 100000
    fixed = {'name': 'S', 'value': f'3^{args.expected_exponent}', 'coordinate': False}
    assert all(d['fixedParameter'] == fixed for d in data.values())
    assert raw['gates'] == translated['gates']
    assert [c['id'] for c in raw['coordinates']] == [c['id'] for c in translated['coordinates']]
    ids = raw['anchor']['privateCoordinateIds']
    assert len(ids) == 3 and len(set(ids)) == 3 and 0 not in ids
    u, v, w = ids
    row_id = raw['anchor']['rowId']
    assert translated['anchor']['rowId'] == row_id
    replacements = {
        u: {(1, ()): Q(1), (0, (u,)): Q(1, 4),
            (0, (v,)): Q(-3, 4), (0, (w,)): Q(3, 4)},
        v: {(1, ()): Q(1, 2), (0, (v,)): Q(1, 4)},
        w: {(1, ()): Q(3, 2), (0, (w,)): Q(1, 4)},
    }
    # Triangular linear part: determinant (1/4)^3 = 1/64 != 0.
    determinant = Q(1, 4)**3
    assert determinant == Q(1, 64)
    r, t = rows(raw), rows(translated)
    assert r.keys() == t.keys()
    for i, p in r.items():
        actual = substitute(p, replacements)
        if i == row_id:
            actual = scale(actual, Q(16))
        else:
            assert not any(set(m) & set(ids) for s, m in p)
        assert actual == t[i]
    for a, b in zip(raw['coordinates'], translated['coordinates']):
        if a['id'] in ids:
            assert {k:v for k,v in a.items() if k!='name'} == {k:v for k,v in b.items() if k!='name'}
        else:
            assert a == b
    assert (root/'compiled/compiled-ir.json').read_bytes() == (root/'final/source-ir.json').read_bytes()
    candidate, integer, final = (data[names[i]] for i in [4, 5, 6])
    assert candidate['coordinates'] == integer['coordinates'] == final['coordinates']
    rational_to_integer = proportional_rows(candidate, integer)
    integer_to_final = proportional_rows(integer, final)
    assert all(Q(f).denominator == 1 for r in rows(integer).values() for f in r.values())
    report = {
        'status': 'PASS',
        'builderSha256': hashlib.sha256((root/'builder.cjs').read_bytes()).hexdigest(),
        'rawIrSha256': hashlib.sha256((root/'raw-ir.json').read_bytes()).hexdigest(),
        'scope': 'Exact stage joins, invertible affine anchor translation and nonzero rational row scalings; no global arithmetic proof.',
        'parameter': fixed,
        'anchorTranslation': {'rowsChecked': len(r), 'privateCoordinates': ids,
                              'determinant': str(determinant), 'anchorRowMultiplier': '16'},
        'compiledSnapshotByteIdentical': True,
        'rationalToIntegerRowScalings': rational_to_integer,
        'integerToFinalRowScalings': integer_to_final,
        'finalCoordinates': len(final['coordinates']),
        'finalResiduals': len(final['residuals']),
        'hashes': {n: hashlib.sha256((root/n).read_bytes()).hexdigest() for n in names},
        'checkerSha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.report.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['status','anchorTranslation','compiledSnapshotByteIdentical','finalCoordinates','finalResiduals','checkerSha256']}))


if __name__ == '__main__':
    main()
