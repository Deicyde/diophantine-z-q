"""Check the frozen printed parent and the two additive aggregate identities.

Reads only inert source/data. Does not import upstream or draft-building code.
"""
from collections import defaultdict
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent
REPO = root.parents[2]
OUT = REPO / 'build/version19'
OUT.mkdir(parents=True, exist_ok=True)
source = REPO / 'manuscripts/quartic_v18.tex'
parent_path = root / 'inputs/jose/computation/quartic/balanced214_v24/source/quadratic214.json'
child_path = root / 'inputs/carbon/family244/family247-intermediate-quadratic.json'
parent = json.loads(parent_path.read_bytes())
child = json.loads(child_path.read_bytes())
text = source.read_text(encoding='utf-8')
assert hashlib.sha256(source.read_bytes()).hexdigest() == '0cb9c70baed00d736c88636243c4da96c38ce4f96090d029d0020ce459435a29'

def decimal_group(match):
    parts = match[1].split(r'\\{}+{}')
    total = 0
    for part in parts:
        m = re.fullmatch(r'(\d+)(?:\\cdot10\^\{(\d+)\})?', part.strip())
        assert m, part
        total += int(m[1]) * 10 ** int(m[2] or 0)
    return str(total)

def printed_polynomial(expression):
    expression = re.sub(r'\\left\(\\begin\{gathered\}(.*?)\\end\{gathered\}\\right\)', decimal_group, expression, flags=re.S)
    expression = expression.replace(r'\\', '').replace(r'\,', '').replace('&', '')
    expression = re.sub(r'\s', '', expression)
    result = defaultdict(int)
    for term in re.findall(r'[+-]?[^+-]+', expression):
        sign = -1 if term.startswith('-') else 1
        term = term.lstrip('+-')
        monomial = []
        for match in re.finditer(r'X_\{(\d+)\}(?:\^\{(\d+)\})?', term):
            monomial.extend([int(match[1])] * int(match[2] or 1))
        term = re.sub(r'X_\{\d+\}(?:\^\{\d+\})?', '', term)
        power = term.count('A_N')
        term = term.replace('A_N', '')
        assert re.fullmatch(r'\d*', term), term
        result[(power, tuple(sorted(monomial)))] += sign * int(term or 1)
    return {key: value for key, value in result.items() if value}

def data_polynomial(row):
    result = defaultdict(int)
    for term in row['terms']:
        result[(term['parameterPower'], tuple(sorted(term['monomial']))) ] += int(term['coefficient'])
    return {key: value for key, value in result.items() if value}

start = text.index(r'\clearpage\section{Complete coordinate and row specification}\label{q214:rows}')
blocks = re.findall(r'\\begin\{equation\*\}\\begin\{aligned\}r_\{(\d+),N\}=\{\}&(.*?)\\end\{aligned\}\\end\{equation\*\}', text[start:], re.S)[:188]
assert [int(i) for i, _ in blocks] == list(range(1, 189))
for row, (number, expression) in zip(parent['residuals'], blocks):
    assert row['id'] == int(number)
    assert printed_polynomial(expression) == data_polynomial(row), number

# z_i = C_i - E_i, with its two rational components. Expand the two
# manuscript aggregate formulas in the 247 coordinate chart, not from
# the row descriptions in Carbon's table.
ids = {coordinate['name']: coordinate['id'] for coordinate in child['coordinates']}
trace = defaultdict(int)
shift = defaultdict(int)
def add(polynomial, coefficient, *variables):
    polynomial[(0, tuple(sorted(variables)))] += coefficient

for i in range(1, 5):
    components = []
    for component in (0, 1):
        suffix = '.rescaled'
        c = ids[f'rootProduct.{i}.C.{component}{suffix}']
        e = ids[f'rootProduct.{i}.E.{component}{suffix}']
        components.append([(c, 1), (e, -1)])
    for component, weight in ((0, 1), (1, 2)):
        for x, cx in components[component]:
            for y, cy in components[component]:
                add(trace, weight * cx * cy, x, y)
    for x, cx in components[0]:
        for y, cy in components[1]:
            add(shift, cx * cy, x, y)

# R_s^2 is the retained square coordinate 117; t_0,t_1,t_2 are 4,90,217.
assert ids['scalar.r_power_2'] == 117
assert data_polynomial(next(row for row in child['residuals'] if row['name'] == 'scalar.r_power_2.definition')) == {(0, (117,)): 1, (0, (118, 118)): -1}
for coefficient, argument in ((8, 4), (-8, 90)):
    add(trace, coefficient, 117, argument)
for coefficient, argument in ((4, 4), (-8, 90), (4, 217)):
    add(shift, coefficient, 117, argument)
rows = {row['name']: row for row in child['residuals']}
for expected, name in ((trace, 'additive.aggregate.rootTrace'), (shift, 'additive.aggregate.rootShift2')):
    assert {key: value for key, value in expected.items() if value} == data_polynomial(rows[name]), name

report = {
    'frozen_v18_printed_parent_rows_match': 188,
    'aggregate_trace_identity': True,
    'aggregate_second_shift_identity': True,
    'upstream_code_executed': False,
    'scope': 'Exact polynomial identities. Does not certify arithmetic or existential proof claims.',
    'inputs': {str(path.relative_to(REPO)): hashlib.sha256(path.read_bytes()).hexdigest() for path in (source, parent_path, child_path)},
    'manuscript_sha256': hashlib.sha256((REPO / 'manuscripts/quartic_v19.tex').read_bytes()).hexdigest(),
}
(OUT / 'interface-verification.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
print(json.dumps(report, indent=2))
