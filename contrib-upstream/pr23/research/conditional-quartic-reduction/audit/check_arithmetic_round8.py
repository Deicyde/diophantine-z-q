"""Portable exact source and numerical checks for the round-eight anchor and refined height.

Imports neither the producer nor compiler. Uniform Euler-product/height, formal-group, norm-parity,
completeness and inherited-global arguments remain in the written proofs.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json, re
from math import prod


def readpoly(terms):
    result = {}
    for term in terms:
        key = (term.get('sPower', 0), tuple(term['monomial']))
        result[key] = result.get(key, F(0)) + F(term['coefficient'])
    return {key: value for key, value in result.items() if value}


def constant(value):
    return {(0, ()): F(value)} if value else {}


def add(*polynomials):
    result = {}
    for polynomial in polynomials:
        for key, value in polynomial.items():
            result[key] = result.get(key, F(0)) + value
    return {key: value for key, value in result.items() if value}


def scale(polynomial, factor):
    return {key: value * F(factor) for key, value in polynomial.items()
            if value * F(factor)}


def multiply(left, right):
    result = {}
    for (s, m), a in left.items():
        for (t, n), b in right.items():
            key = (s + t, tuple(sorted(m + n)))
            result[key] = result.get(key, F(0)) + a * b
    return {key: value for key, value in result.items() if value}


def subtract(left, right):
    return add(left, scale(right, -1))


def normalized(polynomial):
    if not polynomial:
        return ()
    leading = polynomial[min(polynomial)]
    return tuple((key, value / leading) for key, value in sorted(polynomial.items()))


def fieldadd(left, right):
    return tuple(add(a, b) for a, b in zip(left, right))


def fieldsubtract(left, right):
    return tuple(subtract(a, b) for a, b in zip(left, right))


def fieldmultiply(left, right):
    a, b = left
    c, d = right
    return add(multiply(a, c), scale(multiply(b, d), 2)), add(multiply(a, d), multiply(b, c))


def valuation(value, prime):
    value = F(value)
    assert value
    numerator, denominator, answer = abs(value.numerator), value.denominator, 0
    while numerator % prime == 0:
        numerator //= prime
        answer += 1
    while denominator % prime == 0:
        denominator //= prime
        answer -= 1
    return answer


def rational_field_multiply(left, right):
    a, b = left
    c, d = right
    return a*c+2*b*d, a*d+b*c


def rational_field_inverse(value):
    a, b = value
    norm = a*a-2*b*b
    assert norm
    return a/norm, -b/norm


def rational_field_add(left, right):
    return tuple(a+b for a, b in zip(left, right))


def rational_field_scale(value, factor):
    return tuple(a*factor for a in value)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('directory', type=Path)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--proof', type=Path,
                        help='Selected proof to bind; defaults to an adjacent file or ../proofs/arithmetic_round8.tex')
    parser.add_argument('--expected-exponent', type=int, default=2364)
    parser.add_argument('--high-order', type=int, choices=list(range(37,52)), default=45)
    args = parser.parse_args()
    directory = args.directory.resolve()
    proof_candidates = ([args.proof] if args.proof else [
        Path(__file__).resolve().parent/'arithmetic_round8.tex',
        Path(__file__).resolve().parent.parent/'proofs/arithmetic_round8.tex'])
    proof_path = next((path.resolve() for path in proof_candidates if path.is_file()), None)
    assert proof_path is not None, 'selected proof missing; pass --proof PATH'
    raw = directory/'raw-ir.json'
    data = json.loads(raw.read_text())
    values = {name: readpoly(value['terms']) for name, value in data['values'].items()}
    rows = {row['name']: readpoly(row['terms']) for row in data['residuals']}
    coordinates = {coordinate['name']: coordinate for coordinate in data['coordinates']}
    checks = []

    def equal(label, left, right):
        assert left == right, label
        checks.append(label)

    def condition(label, value):
        assert value, label
        checks.append(label)

    def row(name, polynomial):
        equal(name, normalized(rows[name]), normalized(polynomial))

    def field(name):
        return values[name+'.0'], values[name+'.1']

    def fieldconstant(a, b=0):
        return constant(a), constant(b)

    def fieldrow(name, pair):
        for index, polynomial in enumerate(pair):
            row(name+'.'+str(index), polynomial)

    def variable(name):
        return {(0, (coordinates[name]['id'],)): F(1)}

    equal('input remains coordinate0', coordinates['input']['id'], 0)
    parameter = data['fixedParameter']
    equal('fixed parameter is not a coordinate', (parameter['name'], parameter['coordinate']), ('S', False))
    expression = parameter['value']
    match = re.fullmatch(r'3\^\(2\^(\d+)\)', expression)
    if match:
        exponent = 2**int(match[1])
    else:
        match = re.fullmatch(r'3\^(\d+)', expression)
        assert match, 'unsupported fixed parameter syntax'
        exponent = int(match[1])
    equal('declared exact exponent', exponent, args.expected_exponent)
    condition('positive anchor exponent', exponent >= 1)
    gamma = 3 if exponent % 2 == 0 else 1

    X = variable('input')
    row('inputProduct.definition', subtract(values['inputProduct'], add(multiply(X,X),X)))
    equal('input square alias', values['inputSquare'], subtract(values['inputProduct'],X))
    equal('actual beta polynomial', values['beta'], add(scale(values['inputProduct'],11016),constant(5155)))
    equal('actual square-fibre label identity', add(scale(values['inputProduct'],11016),constant(5155)),
          add(scale(add(scale(values['inputProduct'],4),constant(1)),2754),constant(2401)))
    S = {(1, ()): F(1)}
    w = field('scalar.shiftedS.w')
    f = field('scalar.shiftedS.f')
    root = {name: field('S.'+name) for name in ['x', 'h', 'j']}
    P = {'x': fieldconstant(F(57, 8), F(-7, 2)),
         'h': fieldconstant(-1, F(7, 4)),
         'j': fieldconstant(F(39, 8), F(-9, 2))}
    D = fieldconstant(11, -6)
    equal('stored w alias', w, field('scalar.shiftedS.rootTimesInverseRoot'))
    fieldrow('scalar.shiftedS.rootTimesInverseRoot.definition', fieldsubtract(
        fieldmultiply(w, fieldadd(fieldmultiply(P['x'], root['x']), D)),
        fieldsubtract(fieldmultiply(P['h'], fieldmultiply(root['h'], root['j'])),
                      fieldmultiply(root['x'], P['j']))))
    fieldrow('scalar.shiftedS.f.definition', fieldsubtract(fieldmultiply(root['x'], f), fieldmultiply(w, w)))
    for index, polynomial in enumerate(fieldsubtract(root['x'], fieldmultiply(root['h'], root['h']))):
        row('S.chart.x.'+str(index)+'.definition', polynomial)
    row('scalar.shiftedS.nonzeroRealF.definition', subtract(
        multiply(values['scalar.shiftedS.nonzeroRealF'], f[0]), constant(1)))

    physical = add(multiply(w[0], w[0]), scale(multiply(w[1], w[1]), -2),
                   scale(multiply(S, values['heightProduct.scale0']), gamma*4096**2),
                   scale(multiply(S, values['inputSquare']), -2*gamma))
    row('anchor.physicalA.definition', subtract(values['anchor.physicalA'], physical))
    u, v, z = [variable('anchor.'+name) for name in ['u', 'v', 'w']]
    row('anchor.equation', add(multiply(u, u), scale(multiply(v, v), 6),
        scale(multiply(z, z), -2), scale(multiply(values['anchor.physicalA'], values['anchor.physicalA']), -3),
        scale(multiply(S, S), 2)))
    equal('all residuals quadratic with S lifted', max(sp+len(m) for polynomial in rows.values() for sp, m in polynomial), 2)
    for index in range(3):
        condition('detector'+str(index)+' high-order output present', 'detector'+str(index)+'.q'+str(args.high_order) in values)

    equal('norm anisotropic modulo3', [(a,b) for a in range(3) for b in range(3)
          if (a*a-2*b*b)%3 == 0], [(0,0)])
    equal('fourth power of rho modulo3', pow(2, 2, 3), 1)
    condition('all four product leading residues nonzero', all(pow(2, j, 3) != 0 for j in range(5)))
    equal('dyadic product clearing factor', 4096, 2**12)
    condition('doubling error strictly deeper at initial depth', 3*F(3,2) > F(3,2)+1)
    equal('weighted root dyadic minimum after oddness', -F(3,2)+F(5,2), 1)

    # Exact finite calculations underlying the uniform local proofs.
    hp = F(-1), F(7,4)
    jp = F(39,8), F(-9,2)
    xp = rational_field_multiply(hp, hp)
    yp = rational_field_multiply(hp, jp)
    equal('fixed point x from square-root chart', xp, (F(57,8), F(-7,2)))
    equal('fixed point y from root chart', yp, (F(-165,8), F(417,32)))
    zp = rational_field_scale(rational_field_multiply(xp, rational_field_inverse(yp)), -1)
    norm_zp = zp[0]**2-2*zp[1]**2
    equal('fixed point dyadic formal depth', F(valuation(norm_zp, 2), 2), F(3,2))
    slope = rational_field_multiply(rational_field_add(rational_field_scale(rational_field_multiply(xp,xp), 3), (F(-11), F(6))),
                                      rational_field_inverse(rational_field_scale(yp, 2)))
    x2 = rational_field_add(rational_field_multiply(slope,slope), rational_field_scale(xp,-2))
    y2 = rational_field_add(rational_field_multiply(slope,rational_field_add(xp,rational_field_scale(x2,-1))), rational_field_scale(yp,-1))
    z2 = rational_field_scale(rational_field_multiply(x2,rational_field_inverse(y2)), -1)
    equal('literal z2P calculation', z2, (F(3396356159088,3287811625151), F(-4135204317756,3287811625151)))
    equal('both normalized z2P coefficients have depth1', [valuation(t,3) for t in z2], [1,1])
    residue = lambda value: (value.numerator*pow(value.denominator,-1,3))%3
    equal('normalized z2P leading residue', tuple(residue(t/3) for t in z2), (2,1))

    coefficients = [F(1), F(-2,5)]
    for j in range(2,15):
        coefficients.append(coefficients[-1]*F(4*j-5,4*j+1))
    equal('first omitted G12 coefficient', coefficients[13], F(-54756974,6936596275))
    equal('its exact denominator factorization', coefficients[13].denominator, 5**2*7*17*29*37*41*53)
    if args.high_order <= 45:
        condition('full G12 tail linear intercept', F(4*13+1,10) <= 4*13-args.high_order)
    else:
        condition('first G12 tail term at selected order', 52-1 >= args.high_order)
        if args.high_order <= 50:
            condition('remaining G12 tail linear intercept', F(4*14+1,10) <= 4*14-args.high_order)
        else:
            equal('second omitted G12 coefficient', coefficients[14], F(-2881946,408035075))
            equal('second omitted G12 denominator', coefficients[14].denominator, 5**2*7*29*37*41*53)
            condition('second G12 tail term at selected order', 56-1 >= args.high_order)
            condition('remaining G12 tail linear intercept', F(4*15+1,10) <= 4*15-args.high_order)
    condition('positive tail inequality slope', F(4,10) < 4)
    equal('G2 first omitted coefficient retains13 exception', coefficients[3], F(-14,195))

    C = 2**32*3**9
    exceptions = [2,3,5,7,13,17]
    B = prod(exceptions)
    equal('unchanged conductor constant', C, 84537841287168)
    equal('unchanged exceptional product', B, 46410)
    euler_exponent = 192
    alpha = F(18)+F(6,euler_exponent)
    equal('new height exponent', alpha, F(577,32))
    cutoff = 53
    small_primes = [p for p in range(2,cutoff)
                    if all(p % d for d in range(2,p) if d*d <= p)]
    equal('complete finite prime list', small_primes,
          [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47])
    for p in small_primes:
        condition('small normalized Euler factor exceeds1 at'+str(p),
                  (p+1)**euler_exponent > p**(euler_exponent+1))
    condition('uniform Euler cutoff at53',
              (cutoff+1)**euler_exponent < cutoff**(euler_exponent+1))
    small_primorial = prod(small_primes)
    plus_product = prod(p+1 for p in small_primes)
    condition('normalized small-prime Euler coefficient below32/9',
              (9*plus_product)**euler_exponent <
              32**euler_exponent*small_primorial**(euler_exponent+1))
    equal('unchanged T coefficient after Euler refinement', 4608*F(32,9), 2**14)
    equal('genus endpoint d12 g2', F(1)+F(12,12), F(12,6))
    condition('Javanpeykar plus retained remainders below2^22', F(13000000,6)+2 < 2**22)
    condition('Bost remainder belowT^6 at lower endpoint', F(3,2)*16 < 16**6)
    condition('first variation inequality at16 usinglog16<4', 2+4 <= F(16**2,32))
    condition('second variation inequality at16 usinglog16<4', 25+7*4 <= F(16**4,4))
    condition('CM branch dominated forR>=1', 854 < 2**22)
    condition('fixed radical fractional power below3/2', 2**32*B < 3**32)
    H = 3*2**106*C**6*B**18+128
    old_H = 2**110*C**6*B**19+128
    equal('height constant ratio excluding additive128', old_H-128, 247520*(H-128))
    equal('new exact height bit length', H.bit_length(), 665)
    condition('new exact height bound', 4 <= H < 3*2**663)
    index_exponent = (exponent+1)//2-1
    c_min = 2*3**index_exponent
    b_min = c_min-1
    condition('selected anchor exponent remains even', exponent % 2 == 0)
    equal('packing coefficient remains3', gamma, 3)
    condition('scalar28 exact c/4 margin',
              c_min**(28*alpha.denominator-alpha.numerator) > (4*H)**(28*alpha.denominator))
    condition('Lucas exponent is positive', 2*args.high_order > 4*alpha)
    condition('Lucas exact new margin',
              b_min**(2*args.high_order*alpha.denominator-4*alpha.numerator) >
              (24*H)**(args.high_order*alpha.denominator))
    condition('Lucas coefficient estimate', alpha/args.high_order < F(1,2))
    condition('Lucas constant estimate', 21+F(6,4) < 24)
    condition('input height exponent below19', alpha < 19)
    condition('input logarithmic constant bound', 40*H < 2**670)
    condition('input separate logarithmic margin', 100*670 < b_min)
    condition('input affine contradiction endpoint', b_min > 152)
    equal('input consumed coefficient forlabel', F(12,5)*F(1,100)+F(19,5)*F(1,4), F(487,500))
    equal('input consumed additive constant', F(19,5)*F(1,4), F(19,20))
    condition('input final contradiction at152', F(487,500)*152+F(19,20) < 152-3)
    equal('opposite norm parities', ((-exponent)-(1-exponent%2))%2, 1)
    equal('input leading coefficient factorization', 11016, 2**3*3**4*17)
    if exponent == 2364 and args.high_order == 45:
        equal('selected scalar index depth', index_exponent, 1181)
        condition('logarithm3 rational lower bound', 3**53 > 2**84)
        equal('transparent scalar certificate',
              F(319)+F((319*1181-896)*84,53)-665*896, F(8199,53))
        equal('transparent Lucas certificate',
              F((143*1181-720)*84,53)-666*360, F(1418412,53))
        condition('transparent scalar certificate positive', F(8199,53) > 0)
        condition('transparent Lucas certificate positive', F(1418412,53) > 0)
        equal('simple gauge constant exponent', 6*394, exponent)
    chain_records=[]
    for length in [2,3,4]:
        denominator=2**length-1
        seed=(exponent+denominator-1)//denominator
        powers=[seed]*(length-1)
        partial=seed
        for _ in range(length-2):
            partial=2*partial+seed
        powers.append(exponent-2*partial)
        if powers[-1] < 0:
            continue
        chain_exponent=powers[0]
        for multiplier in powers[1:]:
            chain_exponent=2*chain_exponent+multiplier
        equal('scaled chain '+str(powers),chain_exponent,exponent)
        chain_records.append({'coefficientExponents':powers,'terminalExponent':chain_exponent,'coordinates':len(powers),'largestSquaredChainCoefficientDigits':len(str(3**(2*max(powers))))})
    report={'status':'PASS','sourceAssertionsAndFiniteChecks':len(checks),'checks':checks,
        'builderSha256':hashlib.sha256((directory/'builder.cjs').read_bytes()).hexdigest(),
        'rawIrSha256':hashlib.sha256(raw.read_bytes()).hexdigest(),
        'checkerSha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'proofSha256':hashlib.sha256(proof_path.read_bytes()).hexdigest(),
        'fixedParameter':parameter,'anchorExponent':exponent,'forcedIndexThreeExponent':index_exponent,
        'anchorPackingCoefficient':gamma,'minimumIndexBits':c_min.bit_length(),'minimumAbsoluteScalarBits':b_min.bit_length(),
        'highOrder':args.high_order,'requiredScalarConclusion':28,'finiteExceptionalPrimes':exceptions,
        'heightExponent':{'numerator':alpha.numerator,'denominator':alpha.denominator},
        'heightConstant':str(H),'heightConstantBits':H.bit_length(),
        'eulerCertificate':{'power':euler_exponent,'cutoff':cutoff,'smallPrimes':small_primes,
                            'smallPrimorial':str(small_primorial),'plusProduct':str(plus_product),
                            'coefficientUpperBound':'32/9','Tcoefficient':2**14},
        'selectedScalarTarget':'h(beta)<|a-1|/4','inputLogarithmicTarget':'log(40H)<|a|/100',
        'scaledChains':chain_records,
        'scope':'Exact stored-w source chart and anchor equations, local seed calculations, G12 tail constants, scaled-chain exponents, normalized Euler-product certificate, refined height constant and new scalar/Lucas/input numerical margins. The uniform norm/formal-group and height proofs, scalar conclusion, detector source, completeness and inherited globals are reviewed separately.'}
    text=json.dumps(report,indent=2)+'\n'
    if args.report:
        args.report.write_text(text)
    print(text)


if __name__ == '__main__':
    main()
