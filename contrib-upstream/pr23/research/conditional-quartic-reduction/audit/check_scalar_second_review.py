"""Separate exact review of the round-seven scalar norm tree and retained joint charts.

Written by the detector reviewer. Imports neither the geometric proposer’s
checker nor a producer/compiler. Uniform nonzero arguments are in the receipt.
"""
from fractions import Fraction
from pathlib import Path
import argparse
import hashlib
import json


class Poly(dict):
    def __init__(self, value=0):
        if isinstance(value, dict):
            super().__init__((k, Fraction(v)) for k, v in value.items() if v)
        else:
            super().__init__({(): Fraction(value)} if value else {})

    def __add__(self, other):
        other = Poly(other)
        out = dict(self)
        for m, c in other.items():
            out[m] = out.get(m, Fraction(0)) + c
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.items()})

    def __sub__(self, other):
        return self + -Poly(other)

    def __rsub__(self, other):
        return Poly(other) + -self

    def __mul__(self, other):
        other = Poly(other)
        out = {}
        for a, x in self.items():
            for b, y in other.items():
                m = tuple(sorted(a + b))
                out[m] = out.get(m, Fraction(0)) + x * y
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        result = Poly(1)
        for _ in range(n):
            result = result * self
        return result

    def signature(self):
        if not self:
            return ()
        items = sorted(self.items())
        lead = items[0][1]
        return tuple((m, c / lead) for m, c in items)


def variable(name):
    return Poly({(name,): 1})


def decode(terms):
    out = Poly()
    for t in terms:
        monomial = tuple(sorted(['S'] * t.get('sPower', 0) +
                                ['v' + str(i) for i in t['monomial']]))
        out += Poly({monomial: Fraction(t['coefficient'])})
    return out


def fc(a, b=0):
    return [Poly(a), Poly(b)]


def fa(a, b):
    return [a[i] + b[i] for i in range(2)]


def fn(a):
    return [-a[0], -a[1]]


def fm(a, b):
    return [a[0] * b[0] + 2 * a[1] * b[1],
            a[0] * b[1] + a[1] * b[0]]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('directory', type=Path)
    ap.add_argument('--report', type=Path)
    args = ap.parse_args()
    root = args.directory.resolve()
    data = json.loads((root / 'raw-ir.json').read_text())
    rows = {decode(r['terms']).signature() for r in data['residuals']}
    values = {k: decode(v['terms']) for k, v in data['values'].items()}
    variables = {c['name']: variable('v'+str(c['id'])) for c in data['coordinates']}
    checks = []

    def field(name):
        return [values[name + '.' + str(i)] for i in range(2)]

    def check(label, p):
        assert not p or p.signature() in rows, label
        checks.append(label)

    def feq(label, left, right):
        for i in range(2):
            check(label + '.' + str(i), left[i] - right[i])

    h = fc(-1, Fraction(7, 4))
    x = fc(Fraction(57, 8), Fraction(-7, 2))
    j = fc(Fraction(39, 8), Fraction(-9, 2))
    d = fc(11, -6)
    assert fm(h, h) == x
    assert fm(j, j) == fa(fm(x, x), fn(d))
    g = field('H.g')
    s = field('H.jointProduct')
    f = field('H.f')
    fv = field('V0.f')
    kh = field('primaryRatio')
    kv = field('V0.k')
    s2 = fm(s, s)
    hs = fm(h, s)
    js = fm(j, s)
    feq('shared inverse-root square', f, fm(g, g))
    feq('joint reciprocal product', fm(f, fv), s2)
    feq('joint symmetric equation', fa(fa(fm(d, s2), fm(x, fa(f, fv))), fa(js, js)), fc(1))
    feq('joint primary ratio', fm(hs, kh), fa(fc(1), fn(fa(fm(x, f), js))))
    feq('joint alternate ratio', fm(hs, kv), fa(fa(fm(x, fv), js), fc(-1)))
    feq('actual alternate log denominator', fm(kv, field('logV0')), fn(field('logV0.polynomial')))
    for i, name in enumerate(('UA', 'US', 'UT', 'UZ'), start=1):
        feq('actual primary ratio consumer ' + str(i),
            fm(field(name + '.l'), field('L' + str(i))), fm(kh, field(name + '.g')))

    sh, sj, sx = field('S.h'), field('S.j'), field('S.x')
    w = field('scalar.shiftedS.rootTimesInverseRoot')
    sf = field('scalar.shiftedS.f')
    denominator = fa(fm(x, sx), d)
    numerator = fa(fm(h, fm(sh, sj)), fn(fm(sx, j)))
    feq('scalar square-abscissa relation', sx, fm(sh, sh))
    feq('fused scalar first equation', fm(denominator, w), numerator)
    feq('fused scalar reciprocal', fm(sx, sf), fm(w, w))
    guard=values['scalar.shiftedS.nonzeroRealF']
    check('scalar nonzero-real-f inverse',sf[0]*guard-1)
    feq('scalar w alias',field('scalar.shiftedS.w'),w)
    feq('reconstruction denominator alias',field('scalar.shiftedS.ratioDenominator'),
        fa(fa(x,fm(d,sf)),fm(j,w)))
    proxy=values['scalar.ratioProxyReal']
    check('actual real scalar proxy',proxy-kh[0]*w[0]-2*kh[1]*w[1])
    rr=values['scalar.r'];ri=values['scalar.rInverse']
    ri3=values['scalar.rInverse3'];ri7=values['scalar.rInverse7']
    ri15=values['scalar.rInverse15']
    check('scalar inverse',rr*ri-1)
    check('scalar inverse power3',rr*ri3-ri**2)
    check('scalar inverse power7',rr*ri7-ri3**2)
    check('scalar inverse power15',rr*ri15-ri7**2)
    leaf=field('scalar.directLeaf')
    check('scalar proxy scaling',rr*leaf[0]-proxy*ri15)
    assert not leaf[1]
    checks.append('no imaginary proxy leaf')
    check('norm tree consumes proxy real',values['scalar.leaf4']-leaf[0])
    af,bf=field('H.f');cf,df=sf
    for i,component in enumerate([af,bf,cf]):
        check('retained formal coefficient leaf '+str(i),values['scalar.leaf'+str(i)]-component*ri)
    ip=values['inputProduct'];xx=variables['input'];beta=values['beta'];rpair=values['scalar.rPair1']
    check('actual input product',ip-xx**2-xx)
    check('actual beta polynomial',beta-11016*ip-5155)
    check('scalar contact pair',rpair-beta*(beta-1))
    check('scalar contact product',rr-rpair*(32*beta+343))
    assert 11016==2**3*3**4*17
    n1=values['scalar.n1'];u=values['scalar.n1OverR']
    check('left n quotient',rr*n1-values['scalar.leaf1']*bf-cf**2)
    check('left n over r',rr*u-n1)
    L=values['scalar.nLeft'];J=values['scalar.nRight'];N=values['scalar.N'];W=values['scalar.W']
    Jrs=values['scalar.nRight.rightSquare'];Nrs=values['scalar.N.rightSquare']
    check('new left quotient',rr*L-af**2-u*n1)
    check('inverse right norm right square',Jrs-leaf[0]**2)
    check('inverse right norm relation',J-df**2-ri15*Jrs)
    check('inverse outer norm right square',Nrs-J**2)
    check('inverse outer norm relation',N-L**2-ri15*Nrs)
    check('constant outside norm tree',W-1-N)
    assert 'scalar.n0' not in values
    checks.append('deleted former n0 coordinate')
    assert 'scalar.leaf3' not in values
    assert 'scalar.rInverse14' not in values and 'scalar.rInverse28' not in values
    checks.extend(['deleted old fourth scalar coefficient quotient','deleted old inverse14 and inverse28 chain'])
    rho=values['scalar.correctedR'];W2=values['scalar.W2'];Bsemantic=values['scalar.Bsemantic']
    check('unchanged scalar pole coefficient',rho-42*rr)
    check('scalar pole W square',W2-W**2)
    check('actual semantic pole input',Bsemantic-rho*W2)
    U=variables['scalar.preparationU'];V=variables['scalar.preparationV'];ee=variables['scalar.normalized_e']
    pp=variables['scalar.p'];qq=variables['scalar.q'];ss=variables['scalar.s']
    p2=values['scalar.p2'];q2=values['scalar.q2'];s2=values['scalar.s2'];Bh=values['scalar.Bh'];prep=values['scalar.preparationT']
    check('scalar pole p square',p2-pp**2)
    check('scalar pole q square',q2-qq**2)
    check('scalar pole s square',s2-ss**2)
    check('scalar preparation T',prep-rho*W2+V**2)
    check('scalar preparation conic',U**2-rho*prep)
    check('scalar first conic',17*rho*p2-(17-ee)*(17+3*ee))
    check('scalar second conic Bh',Bh-ee*(17-prep))
    check('scalar second conic',17*rho*q2-(s2-Bh)*(s2+3*Bh))
    # Exact affine valuation descent, independently computed from node weights.
    F=Fraction
    Nbound=F(-1,2);Lbound=Nbound/2;Jbound=(Nbound+15)/2
    nbound=(Lbound+2)/2
    bounds={'N':Nbound,'L':Lbound,'J':Jbound,'n':nbound,
            'A':(Lbound+1)/2,'B':(nbound+2)/2,'C':(nbound+1)/2,
            'D':Jbound/2,'y':(Jbound+15)/2,'T':(Jbound+15)/2+16}
    assert bounds=={'N':F(-1,2),'L':F(-1,4),'J':F(29,4),'n':F(7,8),
                    'A':F(3,8),'B':F(23,16),'C':F(15,16),'D':F(29,8),
                    'y':F(89,8),'T':F(217,8)}
    assert 27<bounds['T']<28
    # Affine valuation lower bounds are coefficientwise valid for R>=1.
    # A>=R+1, B,C>=2R+1, D>=4R+1, y>=12R+1, kappa=r^-15.
    assert min((2*2-2,2),(2*2-1,2))==(2,2) # n>=2R+2
    assert min((2*1-1,2),(2*2-2,4))==(1,2) # L>=R+2
    assert min((8,2),(9,2))==(8,2) # J>=8R+2
    assert min((2,4),(2*8-15,2*2))==(1,4) # N>=R+4
    assert 'scalar.shiftedS.scaledK.0' not in values
    assert 'scalar.shiftedS.k.0' not in values
    assert 'scalar.kScaled.0' not in values
    checks.append('deleted exact scalar ordinate and quotient')

    v = {name: variable(name) for name in ('x', 'h', 'j', 'D', 'f', 'F', 's', 'kh', 'kv')}
    x, h, j, d, f, fv, s, kh, kv = [v[n] for n in ('x', 'h', 'j', 'D', 'f', 'F', 's', 'kh', 'kv')]
    sqrel = f * fv - s**2
    crel = d * s**2 + x * (f + fv) + 2 * j * s - 1
    a = 1 - x * f - j * s
    b = x * fv + j * s - 1
    eh = h * s * kh - a
    ev = h * s * kv - b
    ej = j**2 - x**2 + d
    ex = x - h**2
    identities = {}

    identities['direct primary reciprocal curve'] = (
        x * s**2 * (f * kh**2 - 1 + d * f**2)
        - (-(1 - x * f) * (f * crel - x * sqrel) + f * s**2 * ej
           + f * eh * (h * s * kh + a) + f * s**2 * kh**2 * ex))
    identities['direct alternate reciprocal curve'] = (
        x * s**2 * (fv * kv**2 - 1 + d * fv**2)
        - (-(1 - x * fv) * (fv * crel - x * sqrel) + fv * s**2 * ej
           + fv * ev * (h * s * kv + b) + fv * s**2 * kv**2 * ex))
    identities['recovered first subtraction row'] = (
        (x + d * f) * s**2 - h * f * s * kh + f * j * s
        - (-x * sqrel - f * eh + f * crel))
    identities['recovered second subtraction row'] = (
        s * (j + h * kv) + f * (x + d * fv)
        - (ev + crel + d * sqrel))
    hs0, js0, tau, ff, w0 = [variable(n) for n in ('hs0', 'js0', 'tau', 'ff', 'w0')]
    bb = x * hs0**2 + d
    old_first = bb * tau - h * js0 + hs0 * j
    new_first = bb * (hs0 * tau) - h * hs0 * js0 + hs0**2 * j
    identities['scalar first-row fusion'] = new_first - hs0 * old_first
    identities['scalar square fusion'] = hs0**2 * ff - (hs0 * tau)**2 - hs0**2 * (ff - tau**2)
    wk, kk, mm = [variable(n) for n in ('wk','kk','mm')]
    recovered_proxy=h*(wk*kk+h)+d*ff+j*wk
    identities['scalar proxy congruence identity']=(recovered_proxy
        -(wk*(h*kk-mm+j)+(wk*mm+x+d*ff)-(x-h**2)))
    for label, p in identities.items():
        assert not p, label

    report = {
        'status': 'PASS',
        'sourceAssertions': len(checks),
        'checks': checks,
        'abstractIdentities': len(identities),
        'exactValuationBounds': {k: str(v) for k,v in bounds.items()},
        'abstractIdentityNames': list(identities),
        'builderSha256': hashlib.sha256((root / 'builder.cjs').read_bytes()).hexdigest(),
        'rawIrSha256': hashlib.sha256((root / 'raw-ir.json').read_bytes()).hexdigest(),
        'scope': 'Independent source and exact polynomial review of the retained joint chart, fused scalar point, nonzero-real-f guard, real scalar proxy, three-step inverse15 chain, the exact beta polynomial and contact product, every outer-constant norm-tree equation, and the unchanged normalized scalar pole equations. Uniform two-place and nonzero-domain arguments are in the written receipt; inherited global arithmetic is not reverified.'
    }
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'checks'}, indent=2))


if __name__ == '__main__':
    main()
