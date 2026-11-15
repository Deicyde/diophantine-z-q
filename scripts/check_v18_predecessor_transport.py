"""Check printed214 -> additive212 -> reciprocal204 exactly over Q[A].

No upstream generator is imported or executed. The substitutions below are
transcribed from the displayed transport and physical equations. This proves
finite polynomial identities and serialization, not the arithmetic premises.
"""
import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
from itertools import combinations
import json
from math import gcd, lcm, prod
from pathlib import Path
import re


class Poly(dict):
    def __init__(self, value=0):
        entries = value if isinstance(value, dict) else {(0, ()): value}
        super().__init__((key, Fraction(c)) for key, c in entries.items() if c)

    def __add__(self, other):
        values = defaultdict(Fraction, self)
        for key, c in Poly(other).items():
            values[key] += c
        return Poly(values)

    __radd__ = __add__

    def __neg__(self):
        return Poly({key: -c for key, c in self.items()})

    def __sub__(self, other):
        return self + -Poly(other)

    def __rsub__(self, other):
        return Poly(other) + -self

    def __mul__(self, other):
        values = defaultdict(Fraction)
        for (a, m), c in self.items():
            for (b, n), d in Poly(other).items():
                values[a+b, tuple(sorted(m+n))] += c*d
        return Poly(values)

    __rmul__ = __mul__

    def __pow__(self, n):
        if not isinstance(n, int) or n < 0:
            raise ValueError('Only nonnegative integer powers are supported')
        value = Poly(1)
        for _ in range(n):
            value *= self
        return value


def need(condition, message):
    if not condition:
        raise ValueError(message)


def variable(i):
    return Poly({(0, (i,)): 1})


def decode(row):
    result = {}
    for term in row['terms']:
        key = (term['parameterPower'], tuple(term['monomial']))
        need(key[0] >= 0 and key[1] == tuple(sorted(key[1])), 'Noncanonical monomial')
        need(key not in result and Fraction(term['coefficient']) != 0, 'Duplicate or zero term')
        result[key] = Fraction(term['coefficient'])
    return Poly(result)


def serial(p):
    return [{'parameterPower': a, 'monomial': list(m), 'coefficient': str(c)}
            for (a, m), c in sorted(p.items())]


def primitive(p):
    need(bool(p), 'A residual vanished identically')
    denominator = lcm(*(c.denominator for c in p.values()))
    common = gcd(*(int(c*denominator) for c in p.values()))
    factor = Fraction(denominator, common if p[min(p)] > 0 else -common)
    return p * factor


def rename(p, mapping):
    result = defaultdict(Fraction)
    for (a, m), c in p.items():
        result[a, tuple(sorted(mapping[i] for i in m))] += c
    return Poly(result)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def expand_decimal_chunks(match):
    text = re.sub(r'\s+', '', match[1].replace(r'\\', '').replace('{}', ''))
    pieces = text.split('+')
    total = 0
    for piece in pieces:
        part = re.fullmatch(r'(\d+)(?:\\cdot10\^\{(\d+)\})?', piece)
        need(part is not None, 'Unsupported printed decimal chunk')
        total += int(part[1]) * 10**int(part[2] or 0)
    return str(total)


def parse_printed214(source):
    start = source.index(r'\label{q214:rows}')
    end = source.find(r'\section{', start)
    section = source[start:end if end >= 0 else len(source)]
    coordinates = re.findall(r'(\d+) & \\nolinkurl\{([^}]+)\} & (\d+)\\\\', section)
    need([int(c[0]) for c in coordinates] == list(range(1, 215)), 'Printed214 coordinate coverage')
    pattern = (r'\\paragraph\{Row (\d+)\.\} \\nolinkurl\{([^}]+)\}\\nopagebreak\s*'
               r'\\begin\{equation\*\}\\begin\{aligned\}r_\{(\d+),N\}=\{\}&(.*?)'
               r'\\end\{aligned\}\\end\{equation\*\}')
    token = re.compile(r'(?:X_\{(?P<x>\d+)\}(?:\^\{(?P<xe>\d+)\})?'
                       r'|A_N(?:\^\{(?P<ae>\d+)\})?|(?P<n>\d+))')
    rows = []
    for rid, name, equation_id, text in re.findall(pattern, section, re.S):
        need(rid == equation_id, 'Printed row label mismatch')
        text = re.sub(r'\\left\(\\begin\{gathered\}(.*?)\\end\{gathered\}\\right\)',
                      expand_decimal_chunks, text, flags=re.S)
        text = text.replace(r'\\', '').replace(r'\,', '').replace('&', '')
        text = re.sub(r'\s+', '', text)
        if not text.startswith(('+', '-')):
            text = '+' + text
        p = Poly()
        for term in re.findall(r'[+-][^+-]+', text):
            c = Fraction(1 if term[0] == '+' else -1)
            a, m, pos = 0, [], 1
            while pos < len(term):
                match = token.match(term, pos)
                need(match is not None, f'Unsupported printed214 syntax in row {rid}: {term[pos:pos+80]}')
                if match['x'] is not None:
                    i = int(match['x'])
                    need(1 <= i <= 214, 'Printed coordinate out of range')
                    m += [i] * int(match['xe'] or 1)
                elif match['n'] is not None:
                    c *= int(match['n'])
                else:
                    a += int(match['ae'] or 1)
                pos = match.end()
            p += Poly({(a, tuple(sorted(m))): c})
        rows.append({'id': int(rid), 'name': name, 'terms': serial(p)})
    need([r['id'] for r in rows] == list(range(1, 189)), 'Printed214 residual coverage')
    return coordinates, rows


def additive212(rows214):
    x = variable
    roots = [Fraction(1), Fraction(9, 4), Fraction(4), Fraction(2398, 2399)**2, Fraction(439, 407)**2]
    e = [Fraction(1)] + [sum(prod(c) for c in combinations(roots, k)) for k in range(1, 6)]
    replacement = {}
    for arg, r, u, v, s, row in [(4, 76, 77, 78, 80, 22), (90, 91, 92, 93, 95, 35)]:
        t, r, u, v, s = map(x, (arg, r, u, v, s))
        equations = [r-(t-1)**2, u-r*r,
                     v-r*u+e[1]*(1+s)*u-e[2]*(1+s)*r,
                     u*v-(1+s)*(e[3]*u-e[4]*r+e[5])]
        replacement.update({row+i: p for i, p in enumerate(equations)})
    # This is a changed arithmetic aggregate, not a claimed equivalence of
    # the old multiplicative and new additive height arguments.
    aggregate = Poly()
    for c, d in [(161, 163), (175, 177), (189, 191), (203, 205)]:
        aggregate += (x(c)-x(d))**2 + 2*(x(c+1)-x(d+1))**2
    replacement[182] = aggregate - 8*x(117)*(x(90)-x(4))
    kept = [i for i in range(1, 215) if i not in {119, 120}]
    mapping = {old: i+1 for i, old in enumerate(kept)}
    rows = []
    for row in rows214:
        rid = row['id']
        if rid in {64, 65}:
            continue
        p = replacement.get(rid, decode(row))
        need(not any({119, 120}.intersection(m) for _, m in p), 'Deleted212 coordinate remains')
        rows.append({'id': len(rows)+1, 'parent214RowId': rid,
                     'kind': 'replacement' if rid in replacement else 'retained',
                     'terms': serial(primitive(rename(p, mapping)))})
    need(len(rows) == 186, '212 row count')
    return kept, rows


def fadd(*values):
    return tuple(sum((v[i] for v in values), Poly()) for i in (0, 1))


def fscale(value, c):
    return tuple(p*c for p in value)


def fsub(a, b):
    return fadd(a, fscale(b, -1))


def fmul(a, b):
    return a[0]*b[0]+2*a[1]*b[1], a[0]*b[1]+a[1]*b[0]


def field(i, half=False):
    return variable(i), variable(i+1)*(2 if half else 1)


def reciprocal204(rows212):
    weights = {i: 1 for i in [*range(39, 47), *range(48, 52)]}
    weights.update({i: -1 for i in range(205, 209)})
    removed = set(range(155, 169)) | set(range(183, 197))
    removed_rows = set(range(104, 122)) | set(range(140, 158))
    D, one = (Poly(11), Poly(-6)), (Poly(1), Poly())
    S, TH = field(19), field(211)
    new, roots = [], []
    for nr, first, fu, fv, li, lp, kappa in [(1, 213, 54, 23, 31, 33, 1), (3, 223, 58, 27, 39, 41, 2)]:
        f, h, g, k, slope = (field(first+2*i) for i in range(5))
        F, G, L, LP = field(fu, True), field(fv, True), field(li), field(lp)
        equations = [('square.f', fsub(F, fmul(f, f))), ('square.g', fsub(G, fmul(g, g))),
                     ('curve', fadd(fmul(h, h), fscale(f, -1), fmul(D, fmul(f, F)))),
                     ('secant', fsub(fmul(slope, fsub(f, g)), fadd(h, k))),
                     ('tangent', fadd(fmul(slope, fsub(h, k)), fscale(one, -1), fmul(D, fadd(F, fmul(f, g), G))))]
        for side, ordinate, reciprocal, square, ratio, ref in [('primary', h, f, F, L, S), ('alternate', k, g, G, LP, TH)]:
            equations += [(f'ratio.{side}.raw', fadd(fmul(ordinate, ratio), fscale(fmul(reciprocal, ref), kappa))),
                          (f'ratio.{side}.regular', fadd(fmul(fsub(one, fmul(D, square)), ratio), fscale(fmul(ordinate, ref), kappa)))]
        for name, pair in equations:
            for component, p in enumerate(pair):
                new.append({'kind': f'pair{nr}.{name}.{component}', 'terms': serial(primitive(p))})
        roots.append(fadd(fmul(slope, slope), fmul(D, fadd(f, g))))
    aggregate = 8*(variable(4)-variable(90)) + sum((4*r[0] for r in roots), Poly())
    for c, d in [(173, 175), (201, 203)]:
        delta = fsub(field(c), field(d))
        aggregate += fmul(delta, delta)[0]
    formal_ids = [i for i in range(1, 213) if i not in removed] + list(range(213, 233))
    mapping = {old: i+1 for i, old in enumerate(formal_ids)}
    result = []
    for row in rows212:
        rid = row['id']
        if rid in removed_rows:
            continue
        p, low, kind = decode(row), None, 'retained'
        if rid == 180:
            p, kind = aggregate, 'weighted aggregate replacement'
        elif any(set(m).intersection(weights) for _, m in p):
            terms = [(a, sum(weights.get(i, 0) for i in m)+m.count(118)+2*m.count(117),
                      tuple(i for i in m if i not in (117, 118)), c) for (a, m), c in p.items()]
            low = min(e for _, e, _, _ in terms)
            p = Poly()
            for a, e, m, c in terms:
                power = e-low
                need(power in (0, 1, 2), 'Nonquadratic R-power after rescaling')
                m = tuple(sorted(m + (() if power == 0 else ((118,) if power == 1 else (117,)))))
                p += Poly({(a, m): c})
            kind = 'R-rescaled retained'
        need(not any(removed.intersection(m) for _, m in p), 'Deleted204 coordinate remains')
        p = primitive(rename(p, mapping))
        need(max(len(m) for _, m in p) <= 2, 'Nonquadratic204 row')
        result.append({'id': len(result)+1, 'parent212RowId': rid, 'kind': kind,
                       'divided_R_power': low, 'terms': serial(p)})
    for row in new:
        result.append({'id': len(result)+1, 'parent212RowId': None, 'kind': row['kind'],
                       'divided_R_power': None, 'terms': serial(rename(decode(row), mapping))})
    need(len(formal_ids) == 204 and len(result) == 186, '204 dimensions')
    return formal_ids, result


def check(root, manuscript=None):
    source_path = root / 'research/quartic214/construction/artifacts/candidate214-brox/candidate214-ir.json'
    target_path = root / 'research/version18/198/upstream/H10-quartic198/source/computation/quartic/reciprocal204_v27/unbalanced-quadratic.json'
    manuscript = manuscript or root / 'manuscripts/quartic_v18.tex'
    source_raw, target_raw = source_path.read_bytes(), target_path.read_bytes()
    need(digest(source_raw) == 'b15d6477439c3e4be1e98723b69053244debce59e8715683c28fee82aa847ca4', '214 source pin')
    need(digest(target_raw) == '21da11b4a5c9f11d8a3253162283cbd339c0f35599ab9d578a2302009f725536', '204 source pin')
    source, target = json.loads(source_raw), json.loads(target_raw)
    need(len(source['coordinates']) == 214, '214 source coordinate count')
    need(len(source['residuals']) == 188, '214 source residual count')
    need(len(target['coordinates']) == 204, '204 target coordinate count')
    printed_coordinates, printed_rows = parse_printed214(manuscript.read_text(encoding='utf-8'))
    for actual, expected in zip(printed_coordinates, source['coordinates']):
        need((int(actual[0]), actual[1], int(actual[2])) == (expected['id'], expected['name'], expected['parent224Id']), 'Printed214 coordinate mismatch')
    for actual, expected in zip(printed_rows, source['residuals']):
        need(actual['id'] == expected['id'] and actual['name'] == expected['name'] and decode(actual) == decode(expected), f'Printed214 row mismatch {expected["id"]}')
    kept212, rows212 = additive212(printed_rows)
    ids204, rows204 = reciprocal204(rows212)
    need([c['id'] for c in target['coordinates']] == list(range(1, 205)), '204 coordinate order')
    for c, formal in zip(target['coordinates'], ids204):
        if formal <= 212:
            need(c.get('parent212Id') == formal, '204 retained coordinate binding')
    for actual, expected in zip(rows204, target['residuals']):
        need(actual['id'] == expected['id'] and decode(actual) == decode(expected), f'204 coefficient mismatch row {expected["id"]}')
    need(len(target['residuals']) == len(rows204), '204 target row coverage')
    return {'status': 'PASS', 'scope': 'Exact finite transport and printed214 serialization; not arithmetic acceptance.',
            'manuscript_sha256': digest(manuscript.read_bytes()), 'source214_sha256': digest(source_raw),
            'target204_sha256': digest(target_raw), 'printed214_coordinates': 214, 'printed214_rows': 188,
            'additive212_coordinates': kept212, 'additive212_rows': rows212,
            'reciprocal204_formal_ids': ids204, 'reciprocal204_rows': rows204}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    result = check(args.root.resolve())
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print('PASS: all 188 printed214 rows; all 186 additive212 and 186 reciprocal204 rows.')
