"""Portable exact source and numerical checks for the round-seven anchor.

Imports neither the producer nor compiler. Uniform projective-height, formal-group, norm-parity,
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
                        help='Selected proof to bind; defaults to an adjacent file or ../proofs/arithmetic_round7.tex')
    parser.add_argument('--expected-exponent', type=int, default=2790)
    parser.add_argument('--high-order', type=int, choices=list(range(39,52)), default=45)
    args = parser.parse_args()
    directory = args.directory.resolve()
    proof_candidates = ([args.proof] if args.proof else [
        Path(__file__).resolve().parent/'arithmetic_round7.tex',
        Path(__file__).resolve().parent.parent/'proofs/arithmetic_round7.tex'])
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
    H = 2**110*C**6*B**19+128
    equal('unchanged conductor constant', C, 84537841287168)
    equal('unchanged exceptional product', B, 46410)
    equal('exact height bit length', H.bit_length(), 683)
    condition('exact height bound', 4 <= H < 2**683)
    index_exponent = (exponent+1)//2-1
    c_min = 2*3**index_exponent
    b_min = c_min-1
    condition('scalar28 exact old margin', c_min**9 > (80*H)**28)
    condition('Lucas exact old margin', b_min**(2*args.high_order-76) > (24*H)**args.high_order)
    K_numerator=3*H+14
    lucas_polynomial_bound=2*b_min**4+6*b_min**3+5*b_min**2+1
    condition('Lucas exact sharpened margin', (2*(b_min*b_min-6))**args.high_order > K_numerator**args.high_order*lucas_polynomial_bound**19)
    condition('Lucas comparison uniform exponent positive', 2*args.high_order-76 > 0)
    condition('Lucas coefficient estimate exponent', F(19,args.high_order) < F(1,2))
    condition('Lucas coefficient estimate constant', 21+F(6,4) < 24)
    condition('input logarithmic size margin', 40*689 < b_min)
    condition('input orders10 through12 contradiction', 11*b_min > 120)
    equal('opposite norm parities', ((-exponent)-(1-exponent%2))%2, 1)
    equal('two real projective operator factors multiply to7', 2**2*2-1, 7)
    condition('projective rational height constant weaker than retained7H', K_numerator < 14*H)
    if exponent == 2790 and args.high_order == 45:
        condition('logarithm3 rational lower bound', 3**53 > 2**84)
        condition('tight24H binary upper bound', 3*H < 2**684)
        condition('displayed scalar rational margin', F(9,28)*F(117149,53) > 690)
        condition('displayed Lucas rational margin', F(14,45)*F(117096,53) > 687)
        equal('simple gauge constant exponent', 6*465, exponent)
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
        'heightConstantBits':H.bit_length(),'scaledChains':chain_records,
        'scope':'Exact stored-w source chart and anchor equations, local seed calculations, G12 tail constants, scaled-chain exponents and old and sharpened scalar/Lucas/input numerical margins. The uniform norm/formal-group proofs, scalar conclusion, detector source, completeness and inherited globals are reviewed separately.'}
    text=json.dumps(report,indent=2)+'\n'
    if args.report:
        args.report.write_text(text)
    print(text)


if __name__ == '__main__':
    main()
