"""Check the actual cubic alias, changed weight rows and every outside row."""
from copy import deepcopy
from fractions import Fraction as F
from pathlib import Path
import argparse
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'scalar-chain-reduction'))
from check_chain import poly, add, scale, mul


def check(before, after):
    assert before['fixedParameter'] == after['fixedParameter']
    def named(data):
        names = {c['id']: c['name'] for c in data['coordinates']}
        return {r['name']: {(t['sPower'], tuple(sorted(names[i] for i in t['monomial']))):
                            F(t['coefficient']) for t in r['terms']} for r in data['residuals']}
    a, b = named(before), named(after)
    deleted = {f'detector{i}.{n}.definition' for i in range(3) for n in ['mixA', 'mixB', 'mixC', 'mixD']}
    added = {f'detector{i}.{n}.definition' for i in range(3) for n in ['eCubed', 'eSixth', 'eTwelfth']}
    changed = {f'detector{i}.q12.definition' for i in range(3)}
    assert a.keys()-b.keys() == deleted
    assert b.keys()-a.keys() == added
    assert {n for n in a.keys() & b.keys() if a[n] != b[n]} == changed
    def guards(data):
        names = {c['id']: c['name'] for c in data['coordinates']}
        def convert(x, key=None):
            if key == 'monomial': return [names[i] for i in x]
            if isinstance(x, list): return [convert(v) for v in x]
            if isinstance(x, dict): return {k: convert(v, k) for k, v in x.items()}
            return x
        return convert(data['guards'])
    assert guards(before) == guards(after)
    rows = {r['name']: poly(r['terms']) for r in after['residuals']}
    v = {n: poly(p['terms']) for n, p in after['values'].items()}
    def eq(name, lhs, rhs):
        expected = add(lhs, scale(rhs, -1)); actual = rows[name]
        pivot = min(expected)
        assert actual == scale(expected, actual[pivot]/expected[pivot]), name
    one = {(): F(1)}
    # Recompute the five-contact polynomial over Q, independently of the builder.
    cs = [F(1)]
    for root in [F(0), F(1,49), F(1,50), F(1,2450), F(32,1225)]:
        out = [F(0)]*(len(cs)+1)
        for j, c in enumerate(cs): out[j] -= root*c; out[j+1] += c
        cs = out
    x = {(0,): F(1)}
    square = lambda p: mul(p,p)
    for i in range(3):
        p = f'detector{i}'
        t, t2, middle = [v[p+'.'+n] for n in ['t','Fsquare','Fmiddle']]
        eq(p+'.Fsquare.definition', t2, square(t))
        eq(p+'.Fmiddle.definition', middle,
           add(mul(t2,add(t,scale(one,cs[4]))),scale(t,cs[3]),scale(one,cs[2])))
        # Decode the existing affine aliases into Q[x]. Exactly three old
        # coordinates suffice; deltaCubed must introduce no extra coordinate.
        mapping = {}
        def substitute(polynomial):
            result = {}
            for monomial, coefficient in polynomial.items():
                term = scale(one, coefficient)
                for ident in monomial: term = mul(term,mapping[ident])
                result = add(result,term)
            return result
        def identify(value, target):
            unknown = [(m,c) for m,c in value.items() if m and m[0] not in mapping]
            assert len(unknown) == 1 and len(unknown[0][0]) == 1
            monomial, coefficient = unknown[0]
            known = {m:c for m,c in value.items() if m != monomial}
            mapping[monomial[0]] = scale(add(target,scale(substitute(known),-1)),1/coefficient)
        identify(t,x)
        identify(t2,square(x))
        identify(middle,add(mul(square(x),x),scale(square(x),cs[4]),scale(x,cs[3]),scale(one,cs[2])))
        cube = v[p+'.deltaCubed']
        assert all(len(m)<=1 for m in cube)
        assert not any(c['name']==p+'.deltaCubed.quadratic' for c in after['coordinates'])
        delta = add(scale(x,98),scale(one,-1))
        assert substitute(cube) == mul(square(delta),delta)
        eq(p+'.eCubed.definition',v[p+'.eCubed'],mul(v[p+'.q1CubedForWeights'],cube))
        eq(p+'.eSixth.definition',v[p+'.eSixth'],square(v[p+'.eCubed']))
        eq(p+'.eTwelfth.definition',v[p+'.eTwelfth'],square(v[p+'.eSixth']))
        eq(p+'.q12.definition',mul(v[p+'.q12'],v[p+'.eDelta']),square(v[p+'.eTwelfth']))
    return {'deletedRows':sorted(deleted),'addedRows':sorted(added),'changedRows':sorted(changed),
            'unchangedRows':len(a)-len(deleted)-len(changed),'allGuardsUnchanged':True,
            'affineCubesChecked':3}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('before',type=Path);ap.add_argument('after',type=Path)
    ap.add_argument('--report',type=Path,required=True);args=ap.parse_args()
    before,after=[json.loads(p.read_text()) for p in [args.before,args.after]]
    result=check(before,after)
    for name in ['detector0.eCubed.definition','detector1.q12.definition','scalar.N.definition']:
        bad=deepcopy(after);row=next(r for r in bad['residuals'] if r['name']==name)
        row['terms'][0]['coefficient']=str(F(row['terms'][0]['coefficient'])+1)
        try: check(before,bad)
        except (AssertionError,KeyError): pass
        else: raise AssertionError('Accepted mutation: '+name)
    bad=deepcopy(after);bad['values']['detector2.deltaCubed']['terms'][0]['coefficient']='0'
    try: check(before,bad)
    except (AssertionError,KeyError): pass
    else: raise AssertionError('Accepted corrupted cubic alias')
    args.report.write_text(json.dumps({'status':'PASS','independentAcceptance':False,
                                      'comparison':result,'negativeControlsRejected':4},indent=2)+'\n')
    print('PASS: three affine cubic identities, all weight rows, outside consumers and four mutations')


if __name__=='__main__': main()
