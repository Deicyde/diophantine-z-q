"""Exact finite height margins and equality of symbolic source systems.

These checks do not certify the informal height proof or inherited theorem.
"""
from copy import deepcopy
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json

H = 3*2**106*(2**32*3**9)**6*46410**18 + 128
ALPHA = F(577, 32)
OLD = {45: 2130, 47: 2016}
NEW = {45: 2118, 47: 2010}


def margins(order, exponent):
    assert order in NEW and exponent > 0 and exponent % 6 == 0
    c = 2*3**(exponent//2-1)
    b = c-1
    target = F(4) if order == 45 else F(25, 8)
    p = 2*b**4+6*b**3+5*b**2+1
    return {
        'order': order, 'exponent': exponent, 'scalarTarget': str(target),
        'scalar': target.denominator**992*c**415 > (target.numerator*H)**992,
        'lucas': (2*(b*b-6))**(32*order) > (3*H+14)**(32*order)*p**577,
        'auxiliary': 40*H < 2**670 and b > 67000 and b >= 301,
        'monotoneRatioPower': 64*order-2308,
    }


def require_margins(result):
    assert result['scalar'] and result['lucas'] and result['auxiliary']
    assert result['monotoneRatioPower'] > 0


def source_comparison(before, after, order):
    assert before['fixedParameter'] == {'name': 'S', 'value': '3^'+str(OLD[order]), 'coordinate': False}
    assert after['fixedParameter'] == {'name': 'S', 'value': '3^'+str(NEW[order]), 'coordinate': False}
    assert before.keys() == after.keys()
    for key in before.keys()-{'fixedParameter', 'variant'}:
        assert before[key] == after[key], key
    return {'equalSymbolicSections': sorted(before.keys()-{'fixedParameter', 'variant'}),
            'oldExponent': OLD[order], 'newExponent': NEW[order],
            'equalResiduals': len(after['residuals']), 'equalGuards': len(after['guards'])}


def check(before, after, order):
    delta = source_comparison(before, after, order)
    good = margins(order, NEW[order])
    require_margins(good)
    bad = margins(order, NEW[order]-6)
    try:
        require_margins(bad)
    except AssertionError:
        pass
    else:
        raise AssertionError('Preceding insufficient endpoint accepted')
    assert 1-ALPHA/31 == F(415, 992)
    assert 12/(24-ALPHA) == F(384, 191)
    assert ALPHA/(24-ALPHA) == F(577, 191)
    assert F(384,19100)+F(577,191)*F(8,25) == F(4712,4775)
    assert F(4712,4775)*301+F(4616,4775) < 301-3
    assert 3*H+14 < 14*H
    probes = []
    changed = deepcopy(after); changed['fixedParameter']['value'] = before['fixedParameter']['value']
    probes.append(('restore old parameter', changed))
    changed = deepcopy(after); changed['residuals'][0]['terms'][0]['coefficient'] = '999/1'
    probes.append(('change a residual', changed))
    changed = deepcopy(after); changed['guards'] = []
    probes.append(('drop guards', changed))
    changed = deepcopy(after); changed['coordinates'][0]['name'] = 'changed-input'
    probes.append(('rename input', changed))
    for name, changed in probes:
        try:
            source_comparison(before, changed, order)
        except AssertionError:
            pass
        else:
            raise AssertionError('Corruption accepted: '+name)
    return {'status': 'PASS', 'independentAcceptance': False,
            'sourceComparison': delta, 'selectedMargins': good,
            'precedingEndpoint': bad,
            'negativeControlsRejected': ['preceding insufficient endpoint', *[n for n,_ in probes]],
            'scope': 'Exact finite comparisons and unchanged symbolic circuit. Uniform height transfer, completeness and inherited arithmetic require source-level review.'}


def main():
    if not __debug__:
        raise RuntimeError('Run checks without Python optimization')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('before', type=Path)
    ap.add_argument('after', type=Path)
    ap.add_argument('--order', type=int, choices=[45,47], required=True)
    ap.add_argument('--report', type=Path, required=True)
    args = ap.parse_args()
    result = check(json.loads(args.before.read_text()), json.loads(args.after.read_text()), args.order)
    result['files'] = {name: hashlib.sha256(path.read_bytes()).hexdigest()
                       for name,path in [('before',args.before),('after',args.after)]}
    args.report.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: symbolic source equality, three height consumers and five negative controls')


if __name__ == '__main__':
    main()
