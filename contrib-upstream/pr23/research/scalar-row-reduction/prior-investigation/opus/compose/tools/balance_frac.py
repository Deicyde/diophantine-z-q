"""Produce an exact rational diagonal change with S=c^6, c=3^(E/6).

Thirteen existing coordinates change. The input coordinate is fixed.
Each substituted quadratic row is cleared and divided by its integer content;
the new polynomial is the sum of squares of these primitive integer rows.
The separate audit checker does not import this producer.
"""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import argparse
import hashlib
import json
import math
import re
import sys

sys.set_int_max_str_digits(0)

WEIGHTS = {
    'S.chart.h0': 1, 'S.chart.h1': 1,
    'S.chart.x.0.quadratic': 1, 'S.chart.x.1.quadratic': 1,
    'scalar.shiftedS.rootTimesInverseRoot.0': 2,
    'scalar.shiftedS.rootTimesInverseRoot.1': 2,
    'scalar.shiftedS.f.0': 1, 'scalar.shiftedS.f.1': 1,
    'anchor.U': 4, 'anchor.V': 4, 'anchor.W': 4,
    'anchor.physicalA.quadratic': 4,
}
TWO_WEIGHTS = {'S.chart.x.0.quadratic': 1,
               'heightProduct.scale0.quadratic': -21}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2)+'\n')


def main():
    global WEIGHTS,TWO_WEIGHTS
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('construction',type=Path)
    ap.add_argument('--weights',type=Path)
    args=ap.parse_args()
    if args.weights:
        w=json.loads(args.weights.read_text());WEIGHTS=w['three'];TWO_WEIGHTS=w['two']
    root=args.construction.resolve()
    source=root/'final/integer-candidate-ir.json'
    data=json.loads(source.read_text())
    match=re.fullmatch(r'3\^([1-9][0-9]*)',data['fixedParameter']['value'])
    if not match or data['fixedParameter']['coordinate'] is not False:
        raise ValueError('Expected a declared fixed integer 3^E')
    exponent=int(match[1])
    den=int(__import__('os').environ.get('UNIT_DEN','6'))
    if exponent%den:
        raise ValueError('E not divisible by unit denominator')
    unit=exponent//den
    names={c['name']:c['id'] for c in data['coordinates']}
    if not WEIGHTS.keys()<=names.keys():
        raise ValueError('A named scaling coordinate is absent')
    if not TWO_WEIGHTS.keys()<=names.keys():
        raise ValueError('A named dyadic scaling coordinate is absent')
    powers={c['id']:unit*WEIGHTS.get(c['name'],0) for c in data['coordinates']}
    two_powers={c['id']:TWO_WEIGHTS.get(c['name'],0) for c in data['coordinates']}
    if powers[0] or two_powers[0] or data['coordinates'][0]['name']!='input':
        raise ValueError('Input must be unchanged')
    row_certificates=[]
    rows=[]
    polynomial=defaultdict(int)
    for row in data['residuals']:
        substituted=defaultdict(Fraction)
        for term in row['terms']:
            coefficient=int(term['coefficient'])
            m=tuple(term['monomial'])
            power=exponent*term['sPower']+sum(powers[v] for v in m)
            two_power=sum(two_powers[v] for v in m)
            dyadic=Fraction(2**two_power) if two_power>=0 else Fraction(1,2**(-two_power))
            substituted[m]+=coefficient*Fraction(3)**power*dyadic
        substituted={m:a for m,a in substituted.items() if a}
        denominator=math.lcm(*(a.denominator for a in substituted.values()))
        cleared={m:a.numerator*(denominator//a.denominator) for m,a in substituted.items()}
        content=math.gcd(*cleared.values())
        if cleared[min(cleared)]<0:
            content=-content
        divisor=Fraction(content,denominator)
        normalized={m:a//content for m,a in cleared.items()}
        rows.append({'id':row['id'],'name':row['name'],
                     'terms':[{'monomial':list(m),'coefficient':str(a),'sPower':0}
                              for m,a in sorted(normalized.items())]})
        row_certificates.append({'id':row['id'],'divisorNumerator':str(divisor.numerator),
                                 'divisorDenominator':str(divisor.denominator)})
        for m,a in normalized.items():
            for n,b in normalized.items():
                polynomial[tuple(sorted(m+n))]+=a*b
    polynomial={m:a for m,a in polynomial.items() if a}
    ids=sorted(powers)
    compact={v:i for i,v in enumerate(ids)}
    coordinate_data=[{'id':compact[c['id']],'sourceId':c['id'],'name':c['name'],
                      'oldCoordinateEqualsTwoPowerTimesThreePowerTimesNew':True,
                      'twoPower':two_powers[c['id']], 'threePower':powers[c['id']]}
                     for c in sorted(data['coordinates'],key=lambda c:c['id'])]
    active={v for m in polynomial for v in m}
    if active!=set(ids):
        raise ValueError('Inactive coordinate after balancing')
    out=root/'balanced'
    ir={'format':'diagonally-scaled-integer-quadratic-ir-v2',
        'coordinates':data['coordinates'],'residuals':rows,
        'sourceFixedParameter':data['fixedParameter'],
        'inputCoordinate':0}
    poly={'format':'integer-quartic-table-v1','coordinates':coordinate_data,
          'terms':[{'monomial':[compact[v] for v in m],'coefficient':str(a),'sPower':0}
                   for m,a in sorted(polynomial.items())]}
    write_json(out/'integer-ir.json',ir)
    write_json(out/'polynomial.json',poly)
    certificate={
        'format':'diagonal-scaling-certificate-v2',
        'sourceIrSha256':digest(source),'anchorExponent':exponent,
        'cExponent':unit,'direction':'old_x_i = 2^twoPower[i] * 3^threePower[i] * new_x_i',
        'threePowers':{str(v):powers[v] for v in ids},
        'twoPowers':{str(v):two_powers[v] for v in ids},
        'rows':row_certificates,'newIrSha256':digest(out/'integer-ir.json'),
        'polynomialSha256':digest(out/'polynomial.json'),
        'zeroSetArgument':'Every diagonal factor and every row divisor is nonzero. '
                          'The original input is fixed; sums of squares vanish over Q '
                          'exactly when every row vanishes.',
    }
    write_json(out/'diagonal-certificate.json',certificate)
    # Reuse the established atomic text format, not an external library.
    import os
    target=root/f'quartic-{len(ids)}-balanced-decimal.txt'
    temp=target.with_name(target.name+'.tmp')
    with temp.open('w',encoding='utf-8',newline='\n') as stream:
        stream.write('# Fully explicit integer quartic after an invertible diagonal change.\n')
        stream.write(f'# Variables: {len(ids)}; input: x0; degree: 4; monomials: {len(polynomial)}.\n')
        stream.write('# Format: integer coefficient, TAB, monomial; sum all data rows.\n')
        for m,a in sorted(polynomial.items()):
            factors=[]
            for v in sorted(set(m)):
                multiplicity=m.count(v);name=f'x{compact[v]}'
                factors.append(name if multiplicity==1 else f'{name}^{multiplicity}')
            stream.write(f'{a}\t'+('*'.join(factors) or '1')+'\n')
        stream.flush();os.fsync(stream.fileno())
    os.replace(temp,target)
    summary={'coordinates':len(ids),'residuals':len(rows),'degree':max(map(len,polynomial)),
             'monomials':len(polynomial),'integerContent':math.gcd(*polynomial.values()),
             'inputFourthPowerCoefficient':str(polynomial.get((0,0,0,0),0)),
             'maximumCoefficientDigits':max(len(str(abs(a))) for a in polynomial.values()),
             'maximumCoefficientBits':max(abs(a).bit_length() for a in polynomial.values()),
             'scaledCoordinates':sum(powers[i]!=0 or two_powers[i]!=0 for i in ids),
             'ternaryScaledCoordinates':sum(p!=0 for p in powers.values()),
             'dyadicScaledCoordinates':sum(p!=0 for p in two_powers.values()),
             'anchorExponent':exponent,'cExponent':unit,
             'tableSha256':digest(target),'tableBytes':target.stat().st_size,
             'certificateSha256':digest(out/'diagonal-certificate.json')}
    write_json(out/'summary.json',summary)
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    main()
