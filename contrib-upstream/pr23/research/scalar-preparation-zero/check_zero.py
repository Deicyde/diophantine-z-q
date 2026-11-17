"""Author checks of actual preparation-zero rows, domain data and omissions."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'scalar-chain-reduction'))
import check_chain as chain


def check(before, after):
    chain.check(before)
    assert before['coordinates'] == after['coordinates']
    assert before['fixedParameter'] == after['fixedParameter']
    assert before['guards'] == after['guards']
    a = {r['name']: chain.poly(r['terms']) for r in before['residuals']}
    b = {r['name']: chain.poly(r['terms']) for r in after['residuals']}
    assert a.keys() - b.keys() == {'scalar.preparationConic'}
    assert not b.keys() - a.keys()
    changed = {'scalar.preparationT.definition', 'scalar.Bh.definition', 'scalar.secondConic'}
    assert {k for k in b if a[k] != b[k]} == changed
    av, bv = before['values'], after['values']
    assert av.keys() - bv.keys() == {'scalar.U'} and not bv.keys() - av.keys()
    assert {k for k in bv if av[k] != bv[k]} == {
        'scalar.W', 'scalar.W2', 'scalar.Bsemantic', 'scalar.preparationT', 'scalar.Bh'}
    values = {k: chain.poly(v['terms']) for k, v in bv.items()}
    coords = {c['name']: {(c['id'],): F(1)} for c in after['coordinates']}
    v = values.__getitem__
    add, scale, mul = chain.add, chain.scale, chain.mul
    square = lambda x: mul(x, x)
    def eq(name, left, right):
        expected = add(left, scale(right, -1)); actual = b[name]
        assert expected and actual
        pivot = min(expected)
        assert pivot in actual and actual == scale(expected, actual[pivot] / expected[pivot]), name
    assert v('scalar.W') == v('scalar.N')
    assert v('scalar.correctedR') == scale(v('scalar.r'), 42)
    eq('scalar.W2.definition', v('scalar.W2'), square(v('scalar.W')))
    assert v('scalar.Bsemantic') == mul(v('scalar.correctedR'), v('scalar.W2'))
    eq('scalar.preparationT.definition', v('scalar.preparationT'), v('scalar.Bsemantic'))
    eq('scalar.Bh.definition', v('scalar.Bh'),
       mul(coords['scalar.normalized_e'], add({(): F(17)}, scale(v('scalar.preparationT'), -1))))
    eq('scalar.secondConic', add(scale(mul(v('scalar.correctedR'), v('scalar.q2')), 17),
       scale(square(v('scalar.Bh')), 3)),
       add(scale(mul(v('scalar.s2'), v('scalar.Bh')), 2), square(v('scalar.s2'))))
    active = {i for r in after['residuals'] for t in r['terms'] for i in t['monomial']}
    unused = [c for c in after['coordinates'] if c['id'] not in active]
    assert sorted(c['name'] for c in unused) == ['scalar.preparationU', 'scalar.preparationV']
    assert all(c['kind'] == 'base' and not c.get('protected', False) for c in unused)
    return {'changedRows': sorted(changed), 'deletedRows': ['scalar.preparationConic'],
            'unchangedRows': len(b) - len(changed),
            'unusedCoordinates': [c['name'] for c in unused]}


def omit_unused(data, coordinate_map):
    free = set(coordinate_map['omittedFreeCoordinates'])
    removed = [c for c in data['coordinates'] if c['id'] in free]
    assert sorted(c['name'] for c in removed) == ['scalar.preparationU', 'scalar.preparationV']
    assert all(c['kind'] == 'base' and not c.get('protected', False) for c in removed)
    assert not any(free & set(t['monomial']) for r in data['residuals'] for t in r['terms'])
    result = deepcopy(data)
    result['coordinates'] = [c for c in data['coordinates'] if c['id'] not in free]
    assert result['residuals'] == data['residuals']
    return result, removed


def local_claims():
    rho = lambda x: 42*(2401+2754*(2*x+1)**2)*(2400+2754*(2*x+1)**2)*(32*(2401+2754*(2*x+1)**2)+343)
    # Integer polynomials depend only on the input residue at these moduli.
    assert all(rho(x) % 32 == 4 for x in range(32))
    assert all(rho(x) % 243 == 81 for x in range(243))
    assert all(rho(x) % 17 == 13 for x in range(17))
    assert 8**2 % 17 == 13
    return {'rhoMod32': 4, 'rhoMod243': 81, 'rhoMod17': 13,
            'retainedChainAndHeightMargins': chain.margins()}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('before', type=Path)
    ap.add_argument('after', type=Path)
    ap.add_argument('--report', type=Path, required=True)
    args = ap.parse_args()
    before, after = [json.loads(p.read_text()) for p in [args.before, args.after]]
    delta = check(before, after)
    probes = []
    for name in ['scalar.preparationT.definition', 'scalar.Bh.definition', 'scalar.secondConic']:
        bad = deepcopy(after)
        row = next(r for r in bad['residuals'] if r['name'] == name)
        row['terms'][0]['coefficient'] = str(F(row['terms'][0]['coefficient']) + 1)
        probes.append((name, bad))
    bad = deepcopy(after); bad['values']['scalar.W'] = before['values']['scalar.W']
    probes.append(('restore W=1+N', bad))
    bad = deepcopy(after)
    bad['residuals'].append(next(r for r in before['residuals'] if r['name'] == 'scalar.preparationConic'))
    probes.append(('restore preparation conic', bad))
    for name, bad in probes:
        try:
            check(before, bad)
        except (AssertionError, KeyError):
            pass
        else:
            raise AssertionError('Negative control accepted: ' + name)
    report = {'status': 'PASS', 'independentAcceptance': False,
              'beforeSha256': hashlib.sha256(args.before.read_bytes()).hexdigest(),
              'afterSha256': hashlib.sha256(args.after.read_bytes()).hexdigest(),
              'sourceDelta': delta, 'localClaims': local_claims(),
              'negativeControlsRejected': [name for name, _ in probes],
              'scope': 'Exact finite equations, congruences and unchanged scalar chain. Uniform real/finite completeness is a separate author argument.'}
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: preparation-zero rows, outside consumers, local squareclasses, five negative controls')


if __name__ == '__main__':
    main()
