"""Bind checked tables to Version 18 and verify its shifted-square input test.

The complete row parsers and expansions run separately in the same required
CI job. This checks their incorporation and the specific physical identity.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def add(*polynomials):
    out = defaultdict(int)
    for p in polynomials:
        for monomial, coefficient in p.items():
            out[monomial] += coefficient
    return {m: c for m, c in out.items() if c}


def scale(p, n):
    return {m: c*n for m, c in p.items() if c*n}


def mul(p, q):
    out = defaultdict(int)
    for m, a in p.items():
        for n, b in q.items():
            out[tuple(sorted(m+n))] += a*b
    return {m: c for m, c in out.items() if c}


def square(p):
    return mul(p, p)


def variable(i):
    return {(i,): 1}


def substitute(p, mapping):
    out = {}
    for monomial, coefficient in p.items():
        term = {(): coefficient}
        for i in monomial:
            term = mul(term, mapping.get(i, variable(i)))
        out = add(out, term)
    return out


TOKEN = re.compile(r'(?:Y_\{(?P<y>\d+)\}(?:\^\{(?P<e>\d+)\})?|(?P<c>\d+))')


def parse_row(text, family, n):
    pattern = (r'\\label\{q'+str(family)+r':row:'+f'{n:03d}'+r'\}\s*'
               r'\\begin\{aligned\}\s*q_\{'+str(n)+r'\}\^\{\['+str(family)+r'\]\}\s*&=\{\}\s*'
               r'(.*?)\\end\{aligned\}')
    matches = re.findall(pattern, text, re.S)
    need(len(matches) == 1, f'Expected one printed row {family}:{n}')
    rhs = matches[0]
    if r'\mathsf{k}_{1}' in rhs:
        aliases = re.findall(r'\\mathsf\{k\}_\{1\}\s*&=\{\}\s*(\d+)\s*\\end\{aligned\}', text)
        need(len(aliases) == 1, 'Expected one literal k1 definition')
        rhs = rhs.replace(r'\mathsf{k}_{1}', aliases[0])
    rhs = re.sub(r'\s+', '', rhs.replace(r'\\', '').replace('&{}', ''))
    need(bool(rhs), 'Empty row')
    if rhs[0] not in '+-':
        rhs = '+' + rhs
    out = {}
    for term in re.findall(r'[+-][^+-]+', rhs):
        pos = 1
        coefficient = 1 if term[0] == '+' else -1
        monomial = []
        while pos < len(term):
            match = TOKEN.match(term, pos)
            need(match is not None, f'Unparsed row token {family}:{n}:{term[pos:]}')
            if match['y'] is not None:
                i, exponent = int(match['y']), int(match['e'] or 1)
                need(0 <= i < family and 1 <= exponent <= 2, 'Invalid quadratic coordinate')
                monomial.extend([i]*exponent)
            else:
                coefficient *= int(match['c'])
            pos = match.end()
        key = tuple(sorted(monomial))
        need(key not in out, 'Repeated row monomial')
        out[key] = coefficient
    return out


def input_identity(component, family):
    need(family in (198, 196), 'Unexpected family')
    a = add(variable(28), scale(variable(44), -51), {(): -2501})
    b = variable(29)
    i_real = add(a, {(): -3})
    square_real = add(square(a), scale(square(b), 2))
    square_half_imag = mul(a, b)
    need(add(parse_row(component, family, 10), variable(61)) == square_real,
         'Intermediate real square does not represent (I+3)^2')
    need(add(parse_row(component, family, 11), variable(62)) == square_half_imag,
         'Intermediate imaginary square does not represent (I+3)^2')
    i2_real = add(square(i_real), scale(square(b), 2))
    i2_imag = scale(mul(i_real, b), 2)
    expected_real = add(square(i2_real), scale(square(i2_imag), 2))
    expected_imag = scale(mul(i2_real, i2_imag), 2)
    realrow, imagrow, realout, imagout = ((66, 67, 118, 119) if family == 198 else (64, 65, 116, 117))
    mapping = {61: square_real, 62: square_half_imag}
    actual_real = substitute(add(parse_row(component, family, realrow), variable(realout)), mapping)
    actual_imag = substitute(add(parse_row(component, family, imagrow), variable(imagout)), mapping)
    need(actual_real == expected_real, 'Corrected real fourth power is not I^4')
    need(actual_imag == expected_imag, 'Corrected imaginary fourth power is not I^4')
    return {'family': family, 'square_rows': [10, 11],
            'fourth_power_rows': [realrow, imagrow],
            'output_coordinates': [realout, imagout],
            'identity': '(L_1 - (51X^2 + 2504))^4'}


def validate(root=ROOT):
    root = Path(root)
    manuscript_raw = (root/'manuscripts/quartic_v18.tex').read_bytes()
    manuscript = manuscript_raw.decode('utf-8').replace('\r\n', '\n')
    reports = []
    for family in (198, 196):
        path = f'research/version18/{family}/tex/q{family}-rows.tex'
        raw = (root/path).read_bytes()
        component = raw.decode('utf-8').replace('\r\n', '\n')
        need(manuscript.count(component) == 1,
             f'The complete checked {family} table must occur exactly once in the manuscript')
        report = input_identity(component, family)
        reports.append(dict(report, component=path, component_sha256=hashlib.sha256(raw).hexdigest()))
    return {'status': 'PASS', 'source_sha256': hashlib.sha256(manuscript_raw).hexdigest(),
            'tables': reports, 'complete_component_matches': 2,
            'scope': 'Complete checked-component incorporation and exact input-test identities. '
                     'This does not prove the inherited arithmetic or the whole physical interpretation.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    report = validate(args.root)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
