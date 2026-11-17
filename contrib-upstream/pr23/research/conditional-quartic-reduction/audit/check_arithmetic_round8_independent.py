"""Independent exact numerical certificates for the round-eight height argument.

This imports neither the producer, compiler nor the arithmetic author's checker.
The uniform inherited mathematical arguments require the separate written review.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import isqrt, prod
import argparse
import hashlib
import json


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--proof', type=Path, required=True)
    ap.add_argument('--directory', type=Path)
    ap.add_argument('--report', type=Path, required=True)
    args = ap.parse_args()
    if not __debug__:
        raise RuntimeError('Run with Python assertions enabled')
    checks = []
    def check(label, statement):
        assert statement, label
        checks.append(label)

    small = [p for p in range(2, 53)
             if all(p % d for d in range(2, isqrt(p)+1))]
    listed = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]
    check('complete small-prime list by independent trial division', small == listed)
    for p in small:
        check('normalized Euler factor exceeds one at '+str(p), (p+1)**192 > p**193)
    check('cutoff53 Euler inequality', 54**192 < 53**193)
    numerator = prod(p+1 for p in small)
    denominator = prod(small)
    check('normalized fifteen-prime product less than32/9',
          (9*numerator)**192 < 32**192*denominator**193)
    check('level-character-Euler coefficient', Q(4608*32,9) == 2**14)
    alpha = Q(577,32)
    check('degree exponent multiplied by six', 6*(3+Q(1,192)) == alpha)
    check('genus bound difference', Q(1,6)-Q(1,12) == Q(1,12))
    check('genus threshold from g>=2', 12*(2-1) == 12)
    check('formal minimumT', 2**14 >= 16)
    check('Jacobian bound remains below old2^24', Q(13_000_000,6) < 2**24)
    check('Faltings coefficient after variation and complement', Q(13_000_000,6)+2 < 2**22)
    check('Faltings power-of-two coefficient', 22+6*14 == 106)
    check('variation first endpoint using log16<4', 2+4 < Q(16**2,32))
    check('variation first derivative threshold', 16**2 > 16)
    check('variation second endpoint using log16<4', 25+7*4 < Q(16**4,4))
    check('variation second derivative threshold', 16**4 > 7)
    check('variation two summands giveT^6', Q(16,32)+Q(2,4) == 1)
    check('Bost complement absorbed atT16', Q(3*16,2) < 16**6)
    check('CM estimate absorbed forR>=1', 854 < 2**106)

    exceptional = [2,3,5,7,13,17]
    B = prod(exceptional)
    C = 2**32*3**9
    check('exceptional product', B == 46410)
    check('fixed radical fractional power below3/2', 2**32*B < 3**32)
    H = 3*2**106*C**6*B**18+128
    H7 = 2**110*C**6*B**19+128
    check('new height constant bit length', H.bit_length() == 665)
    check('stated sharper height binary bound', H < 3*2**663)
    check('preceding height constant comparison', H7-128 == 247520*(H-128))
    check('height constant dominates scale additive allowance', H >= 4)
    check('elementary log50 upper bound from e>8/3', Q(8,3)**4 > 50)
    check('scale additive allowance below16', 3*4+Q(5,2) < 16)
    check('order of global height exponent', 18 < alpha < 19)
    check('scalar power gap', 1-alpha/28 == Q(319,896))
    check('Lucas power gap', 2-4*alpha/45 == Q(143,360))
    check('Lucas constant square-root allowance', alpha/45 < Q(1,2) and 5 < 9)
    check('Lucas additive6 allowance', 6 < 3*H)
    check('input power denominator positive', alpha/12 < 2)
    check('input40H allowance', 7*4*H+6 < 40*H)
    check('input first coefficient bounded by12/5', 12/(24-alpha) < Q(12,5))
    check('input second coefficient bounded by19/5', alpha/(24-alpha) < Q(19,5))

    E = 2364
    cstar = 2*3**(E//2-1)
    bstar = cstar-1
    check('selected exponent is even and divisible by six', E % 6 == 0)
    check('selected anchor depth', E//2-1 == 1181)
    check('selected balancing exponent', E//6 == 394)
    check('logarithm3 lower certificate', 3**53 > 2**84)
    scalar_margin = 319+(319*1181-896)*Q(84,53)-665*896
    lucas_margin = (143*1181-720)*Q(84,53)-666*360
    check('displayed scalar rational certificate', scalar_margin == Q(8199,53) and scalar_margin > 0)
    check('displayed Lucas rational certificate', lucas_margin == Q(1418412,53) and lucas_margin > 0)
    check('direct scalar integer inequality', cstar**319 > (4*H)**896)
    check('direct Lucas integer inequality', bstar**143 > (24*H)**360)
    check('height24 coefficient bound', 24*H < 9*2**666)
    check('height40 coefficient bound', 40*H < 2**670)
    check('input logarithmic margin', 100*670 < bstar)
    check('input linear contradiction threshold', bstar > 152)
    check('input linear coefficient', Q(12,5*100)+Q(19,5*4) == Q(487,500))
    check('input constant coefficient', Q(19,5*4) == Q(19,20))
    check('last contradiction at152', (1-Q(487,500))*152 > 3+Q(19,20))
    check('input quadratic coefficient support', 11016 == 2**3*3**4*17)

    source = None
    if args.directory:
        d = args.directory.resolve()
        raw = json.loads((d/'raw-ir.json').read_text())
        check('actual selected fixed parameter', raw['fixedParameter'] == {'name':'S','value':'3^2364','coordinate':False})
        source = {'builderSha256':sha(d/'builder.cjs'), 'rawIrSha256':sha(d/'raw-ir.json')}
    report = {
        'status':'PASS', 'independentExactChecks':len(checks), 'checks':checks,
        'alpha':str(alpha), 'heightConstantBits':H.bit_length(),
        'heightConstantSha256':hashlib.sha256(str(H).encode()).hexdigest(),
        'anchorExponent':E, 'forcedThreeExponent':1181,
        'scalarRationalMargin':str(scalar_margin), 'LucasRationalMargin':str(lucas_margin),
        'smallPrimeProductNumerator':str(numerator), 'smallPrimeProductDenominator':str(denominator),
        'proofSha256':sha(args.proof), 'checkerSha256':sha(Path(__file__)),
        'sourceBinding':source,
        'scope':'Exact independent inequalities and parameter binding for the written conditional reapplication. The Euler tail monotonicity, modular/genus conventions, inherited global inputs, formal anchor argument and consumers are addressed in the separate review; these computations do not prove them.',
    }
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
