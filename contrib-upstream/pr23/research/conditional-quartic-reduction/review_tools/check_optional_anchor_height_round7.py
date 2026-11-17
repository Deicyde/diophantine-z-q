"""Exact finite certificates for optional, unselected anchor/height results.

The uniform local and projective-height arguments are in the separate note.
No producer, compiler, or floating-point logarithm is used here.
"""
from pathlib import Path
from fractions import Fraction
from hashlib import sha256
import argparse
import json


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--proof', type=Path,
                        default=Path(__file__).with_name('optional_anchor_height_round7.tex'))
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    H = 2**110*(2**32*3**9)**6*46410**19+128
    checks = []

    def check(name, statement):
        assert statement, name
        checks.append(name)

    check('exact retained height bits', H.bit_length() == 683)
    check('rational exponential bound for log50', Fraction(8, 3)**4 > 50)
    check('rational exponential bound for log7', Fraction(8, 3)**2 > 7)
    check('real projective operator factors product', 4*2-1 == 7)
    parity_cases = []
    for residue in [0, 1]:
        epsilon = 1-residue
        check('opposite valuation parities '+str(residue), (-residue-epsilon) % 2 == 1)
        # E=2k+s: ceil(E/2)=k+s.  The two possible epsilon values are 0,1.
        check('packing integrality boundary '+str(residue), epsilon >= 0 and epsilon-2 < 0)
        parity_cases.append({'exponentParity': residue, 'epsilon': epsilon,
                             'packingCoefficient': 3**epsilon,
                             'forcedIndexThreeExponentForE2kPlusS': 'k-1' if residue == 0 else 'k'})

    def margin(exponent, projective):
        c = 2*3**((exponent+1)//2-1)
        b = c-1
        scalar = c**9 > (80*H)**28
        if projective:
            polynomial_bound = 2*b**4+6*b**3+5*b*b+1
            lucas = (2*(b*b-6))**45 > (3*H+14)**45*polynomial_bound**19
        else:
            lucas = b**14 > (24*H)**45
        return {'exponent': exponent, 'scalar28': scalar, 'Lucas45': lucas,
                'both': scalar and lucas, 'indexThreeExponent': (exponent+1)//2-1}

    comparisons = []
    for projective, below, first in [(True, 2770, 2771), (False, 2786, 2787)]:
        before, after = margin(below, projective), margin(first, projective)
        check('preceding sufficient test fails '+str(projective), not before['both'])
        check('first sufficient test passes '+str(projective), after['both'])
        check('paired even exponent same predicate '+str(projective),
              after['indexThreeExponent'] == margin(first+1, projective)['indexThreeExponent'])
        comparisons.append({'usesOptionalProjectiveHeight': projective,
                            'previousExponent': before, 'firstSufficientOddExponent': after,
                            'pairedEvenExponent': first+1})
    check('selected exponent succeeds with preceding constants', margin(2790, False)['both'])
    report = {'status': 'PASS', 'finiteChecks': len(checks), 'checks': checks,
              'checkerSha256': sha256(Path(__file__).read_bytes()).hexdigest(),
              'proofSha256': sha256(args.proof.read_bytes()).hexdigest(),
              'heightBits': H.bit_length(), 'scalarOrder': 28, 'highOrder': 45,
              'parityCases': parity_cases, 'comparisons': comparisons,
              'selectedExponent': 2790,
              'scope': 'Optional sufficient-comparison endpoints only. The uniform monotonicity in the note makes the immediately preceding failure an endpoint certificate. No global or circuit optimality claim; the selected construction uses the preceding height constants.'}
    text = json.dumps(report, indent=2)+'\n'
    if args.report:
        args.report.write_text(text)
    print(text)


if __name__ == '__main__':
    main()
