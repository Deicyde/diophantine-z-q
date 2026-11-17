"""Adapted copy of construction/balance_coefficients.py: exact diagonal change
old_x_i = 2^b_i 3^a_i new_x_i with arbitrary integer (possibly negative) a_i,b_i read
from a JSON {name: [a,b]}; rows cleared and made primitive; SOS expanded exactly."""
from collections import defaultdict
from fractions import Fraction
import json, math, sys, re, hashlib
sys.set_int_max_str_digits(0)
def balance(data, powers_by_name, want_poly=True):
    E=int(re.fullmatch(r'3\^(\d+)',data['fixedParameter']['value'])[1])
    a={c['id']:int(powers_by_name.get(c['name'],[0,0])[0]) for c in data['coordinates']}
    b={c['id']:int(powers_by_name.get(c['name'],[0,0])[1]) for c in data['coordinates']}
    assert a[0]==0 and b[0]==0
    rows=[]; rowmax=[]
    for row in data['residuals']:
        sub=defaultdict(Fraction)
        for t in row['terms']:
            c=Fraction(t['coefficient']); m=tuple(sorted(t['monomial']))
            s=Fraction(t['sPower']); assert s.denominator==1
            p3=E*int(s)+sum(a[v] for v in m); p2=sum(b[v] for v in m)
            sub[m]+=c*(Fraction(3)**p3)*(Fraction(2)**p2)
        sub={m:x for m,x in sub.items() if x}
        den=math.lcm(*(x.denominator for x in sub.values()))
        cl={m:x.numerator*(den//x.denominator) for m,x in sub.items()}
        g=math.gcd(*cl.values())
        norm={m:x//g for m,x in cl.items()}
        rows.append((row['name'],norm)); rowmax.append((max(abs(x) for x in norm.values()),row['name']))
    out={'rowMaxDigits':sorted(((len(str(x)),n) for x,n in rowmax),reverse=True)[:8]}
    if want_poly:
        poly=defaultdict(int)
        for _,norm in rows:
            items=list(norm.items())
            for i,(m,x) in enumerate(items):
                poly[tuple(sorted(m+m))]+=x*x
                for (n,y) in items[i+1:]:
                    poly[tuple(sorted(m+n))]+=2*x*y
        poly={m:x for m,x in poly.items() if x}
        mx=max(abs(x) for x in poly.values())
        argmax=[m for m,x in poly.items() if abs(x)==mx]
        names={c['id']:c['name'] for c in data['coordinates']}
        active={v for m in poly for v in m}
        out.update({'coordinates':len(data['coordinates']),'activeCoordinates':len(active),'residuals':len(rows),
            'monomials':len(poly),'degree':max(map(len,poly)),'integerContent':math.gcd(*poly.values()),
            'inputFourthPowerCoefficient':str(poly.get((0,0,0,0),0)),
            'maximumCoefficientDigits':len(str(mx)),'maximumCoefficientBits':mx.bit_length(),
            'maxCoefficientFactor':factor23(mx),
            'argmax':[[names[v] for v in m] for m in argmax[:3]]})
        out['_poly']=poly
    return out
def factor23(x):
    x=abs(x); e3=e2=0
    while x%3==0: x//=3; e3+=1
    while x%2==0: x//=2; e2+=1
    return '%d * 2^%d * 3^%d'%(x,e2,e3)
if __name__=='__main__':
    data=json.load(open(sys.argv[1])); pw=json.load(open(sys.argv[2])) if len(sys.argv)>2 else {}
    r=balance(data,pw); r.pop('_poly'); print(json.dumps(r,indent=1))
