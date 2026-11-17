"""Separate exact source review of the round-seven detector normalization.

Written by the arithmetic reviewer using its independently maintained polynomial helper. Imports neither the geometric proposer’s
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
    ap=argparse.ArgumentParser()
    ap.add_argument('directory',type=Path)
    ap.add_argument('--proof',type=Path)
    ap.add_argument('--report',type=Path)
    args=ap.parse_args()
    root=args.directory.resolve()
    data=json.loads((root/'raw-ir.json').read_text())
    rows={decode(r['terms']).signature() for r in data['residuals']}
    values={k:decode(v['terms']) for k,v in data['values'].items()}
    variables={c['name']:variable('v'+str(c['id'])) for c in data['coordinates']}
    checks=[]
    def field(name):return [values[name+'.'+str(i)] for i in range(2)]
    def check(label,p):
        assert not p or p.signature() in rows,label
        checks.append(label)
    def feq(label,left,right):
        for j in range(2):check(label+'.'+str(j),left[j]-right[j])
    def conjugate(x):return [x[0],-x[1]]
    expected=[field(n+'.g') for n in ['H','UA','US','UT','UZ']]
    expected += [conjugate(field('V'+str(i)+'.f')) for i in range(5)]
    expected += [fa(field('L'+str(i)),fn(conjugate(field('LP'+str(i))))) for i in range(1,5)]
    expected += [[field('L1')[0]-values['beta'],field('L1')[1]], [values['Lucas.F0'],values['Lucas.F1']]]
    tests={1:[],12:[],45:[]}
    for i,want in enumerate(expected):
        assert field('test'+str(i))==want
        checks.append('retained underlying test '+str(i))
        order=12 if i==10 else 45 if i==0 or i>=11 else 1
        index=len(tests[order]);actual=field('testSquare.'+str(order)+'.'+str(index))
        feq('actual squared test '+str(i),actual,fm(want,want))
        tests[order].append(actual)
    mixed_one=tests[1][0];mixed_low=tests[12][0]
    mixed_product=field('mixedTestProduct')
    feq('mixed coefficient product',mixed_product,fm(mixed_one,mixed_low))
    lam=variables['lambda']
    check('positive lambda chart',lam-Fraction(32,1225)-variables['lambda.positiveA']**2-variables['lambda.positiveB']**2)
    c0,c1=field('heightProduct')
    scale0,scale1=values['heightProduct.scale0'],values['heightProduct.scale1']
    check('retained scale0',scale0-c0**2)
    check('retained scale1',scale1-(c0+c1)**2)
    contacts=[Fraction(0),Fraction(1,49),Fraction(1,50),Fraction(1,2450),Fraction(32,1225)]
    coeff=[Fraction(1)]
    for theta in contacts:
        nxt=[Fraction(0)]*(len(coeff)+1)
        for j,a in enumerate(coeff):nxt[j]-=theta*a;nxt[j+1]+=a
        coeff=nxt
    for i,scale in enumerate([Poly(1),scale0,scale1]):
        prefix='detector'+str(i)
        val=lambda suffix:values[prefix+'.'+suffix]
        t=val('t');delta=98*t-1
        check(prefix+' scaled lambda',t-scale*lam)
        t2,middle,ft=val('Fsquare'),val('Fmiddle'),val('F')
        check(prefix+' contact square',t2-t**2)
        check(prefix+' contact middle',middle-t2*(t+coeff[4])-coeff[3]*t-coeff[2])
        check(prefix+' contact product',ft-t2*middle-coeff[1]*t-coeff[0])
        ad,ad2,ad4=val('Adelta'),val('Adelta4.half.square'),val('Adelta4.square')
        check(prefix+' A delta',ad-scale*delta)
        check(prefix+' A delta square',ad2-ad**2)
        check(prefix+' A delta fourth',ad4-ad2**2)
        q1,E=val('q1'),val('eDelta')
        check(prefix+' direct new q1',q1*ft-scale*ad4)
        delta2=val('delta2')
        check(prefix+' reused guard square',delta2-delta**2)
        check(prefix+' exact unchanged reciprocal R',E-q1*delta2)
        square,cube=val('q1SquaredForWeights'),val('q1CubedForWeights')
        check(prefix+' order1 square',square-q1**2)
        check(prefix+' order1 cube',cube-square*q1)
        assert square==val('E1.power2') and cube==val('E1.power3')
        checks.append(prefix+' actual square and cube reuse')
        a,b,c,d=[val('mix'+letter) for letter in 'ABCD']
        q12,high_square,q45=val('q12'),val('mixedHigh'),val('q45')
        check(prefix+' weight a',a-E**2)
        check(prefix+' weight b',b-a*E)
        check(prefix+' weight c',c-b*cube)
        check(prefix+' weight d',d-c**2)
        check(prefix+' weight low',E*q12-d**2)
        check(prefix+' high square',high_square-q12**2)
        check(prefix+' weight high',cube*q45-high_square**2)
        qmix=val('q1q12')
        check(prefix+' mixed product weight',qmix-q1*q12)
        mixed=field(prefix+'.mixed')
        want=[1+q1*mixed_one[0]+q12*mixed_low[0]+qmix*mixed_product[0],
              q1*mixed_one[1]+q12*mixed_low[1]+qmix*mixed_product[1]]
        feq(prefix+' actual mixed product',mixed,want)
        pure=field(prefix+'.pure');W=field(prefix+'.W')
        feq(prefix+' actual pure product',pure,fm(field(prefix+'.E1'),field(prefix+'.E45')))
        feq(prefix+' actual total product',W,fm(pure,mixed))
        norm_quotient,B=val('normOver2w0'),val('B')
        check(prefix+' actual trace inverse',2*W[0]*norm_quotient-W[0]**2+2*W[1]**2)
        check(prefix+' actual pole input',E*B-norm_quotient**2)
        assert val('Bsemantic')==B
        checks.append(prefix+' semantic pole alias')
        p,q,s,e=[variables[prefix+'.'+name] for name in ['p','q','s','normalized_e']]
        p2,q2,s2,Bh=[val(name) for name in ['p2','q2','s2','Bh']]
        check(prefix+' pole p square',p2-p**2)
        check(prefix+' pole q square',q2-q**2)
        check(prefix+' pole s square',s2-s**2)
        check(prefix+' pole first conic',17*B*p2-(17-e)*(17+3*e))
        check(prefix+' pole Bh',Bh-e*(17-B))
        check(prefix+' pole second conic',17*B*q2-(s2-Bh)*(s2+3*Bh))
        assert prefix+'.eWeight' not in values and prefix+'.delta3' not in values
        checks.append(prefix+' deleted old stored e and delta3')
    guard_values=[98*x-1 for x in contacts]
    assert guard_values==[Fraction(-1),Fraction(1),Fraction(24,25),Fraction(-24,25),Fraction(39,25)]
    assert guard_values[-1]>0 and min(contacts[-1]-x for x in contacts)>=0
    # Laurent pairs are (e exponent, delta exponent), reconstructed separately.
    op=lambda x,y,z=(0,0):tuple(a+b-c for a,b,c in zip(x,y,z))
    E=(1,1);q1=(1,-1);cube=op(op(q1,q1),q1)
    a=op(E,E);b=op(a,E);c=op(b,cube);d=op(c,c);low=op(d,d,E);h=op(low,low);high=op(h,h,cube)
    laurent=[a,b,c,d,low,h,high]
    assert laurent==[(2,2),(3,3),(6,0),(12,0),(23,-1),(46,-2),(89,-1)]
    normalization=[]
    for m in [1,12,45]:
        # R^(1-2m) * delta^(-2m), where R=(e delta)^-1.
        pair=(2*m-1,2*m-1-2*m)
        assert pair==(2*m-1,-1)
        # Local valuation from v(e)=5(eta+alpha), v(delta)=eta+alpha-nu.
        local=(1,5*(2*m-1)-1,5*(2*m-1)-1)
        assert local==(1,10*m-6,10*m-6)
        normalization.append({'order':m,'weight':list(pair),'smallPrimeValuationInNuEtaAlpha':list(local),'realLambdaPower':-1})
    assert data['fixedParameter']=={'name':'S','value':'3^2790','coordinate':False}
    report={'status':'PASS','sourceAssertions':len(checks),'checks':checks,'laurentIdentities':len(laurent),'normalizationIdentities':len(normalization),'laurentPairs':laurent,'normalization':normalization,'guardValues':[str(v) for v in guard_values],
        'builderSha256':hashlib.sha256((root/'builder.cjs').read_bytes()).hexdigest(),
        'rawIrSha256':hashlib.sha256((root/'raw-ir.json').read_bytes()).hexdigest(),
        'checkerSha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'reviewedProofSha256':hashlib.sha256(args.proof.read_bytes()).hexdigest() if args.proof else None,
        'scope':'Independent exact reconstruction of all semantic test aliases and squares, the changed weight/contact equations, mixed product, actual trace and normalized pole consumers, guard values and Laurent/local exponents. Uniform real/progression, one-place and completeness arguments are reviewed in the accompanying receipt; inherited global inputs are not reverified.'}
    if args.report:args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='checks'},indent=2))

if __name__=='__main__':main()
