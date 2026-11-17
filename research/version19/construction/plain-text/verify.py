"""Independently serialize and parse the existing 250-variable coefficient table.

Verify the committed plain-algebra expression against every coefficient.
The repository record policy is defined separately.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / 'coefficients/quartic250-decimal.json'
raw = SOURCE.read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'd5373b246be965e56c54764c142fded807ce6f82c095d90584a1909e804f718c'
data = json.loads(raw)
assert data['variables'] == 250 and data['degree'] == 4
terms = {}
for row in data['terms']:
    assert re.fullmatch(r'-?[1-9][0-9]*', row['coefficient'])
    monomial = tuple(row['monomial'])
    assert len(monomial) <= 4 and tuple(sorted(monomial)) == monomial
    assert all(type(v) is int and 1 <= v <= 250 for v in monomial)
    assert monomial not in terms
    terms[monomial] = int(row['coefficient'])
assert len(terms) == data['nonzeroMonomials'] == 3362

parts = []
for monomial, coefficient in sorted(terms.items()):
    variables = [f'x{v}' + (f'^{e}' if e > 1 else '')
                 for v, e in sorted(Counter(monomial).items())]
    factors = variables[:]
    if abs(coefficient) != 1 or not monomial:
        factors.insert(0, str(abs(coefficient)))
    sign = '-' if coefficient < 0 else '+' if parts else ''
    parts.append(sign + '*'.join(factors))
text = ''.join(parts)
encoded = text.encode('ascii')
assert not any(c.isspace() for c in text)

# Parse the serialized expression through a separate grammar, without eval.
# Recover every integer coefficient and repeated-index monomial exactly.
parsed = {}
chunks = re.findall(r'[+-]?[^+-]+', text)
assert ''.join(chunks) == text
for chunk in chunks:
    sign = -1 if chunk.startswith('-') else 1
    body = chunk[1:] if chunk[0] in '+-' else chunk
    factors = body.split('*')
    coefficient = sign
    if re.fullmatch(r'[1-9][0-9]*', factors[0]):
        coefficient *= int(factors.pop(0))
    monomial = []
    for factor in factors:
        match = re.fullmatch(r'x([1-9][0-9]*)(?:\^([2-4]))?', factor)
        assert match is not None, factor
        variable = int(match[1])
        exponent = int(match[2] or '1')
        assert 1 <= variable <= 250
        monomial.extend([variable] * exponent)
    key = tuple(monomial)
    assert key == tuple(sorted(key)) and key not in parsed
    parsed[key] = coefficient
assert parsed == terms
assert max(map(abs, parsed.values())) == int(data['maxAbsCoefficient'])
assert max(map(len, parsed)) == 4
assert set(v for monomial in parsed for v in monomial) == set(range(1, 251))

# Count disjoint character classes independently of the byte-length measurement.
counts = {
    'digits': sum(c.isdigit() for c in text),
    'variable_markers': text.count('x'),
    'multiplication_signs': text.count('*'),
    'exponent_markers': text.count('^'),
    'plus_signs': text.count('+'),
    'minus_signs': text.count('-'),
}
assert sum(counts.values()) == len(encoded) == 85737
output = ROOT / 'quartic250-decimal.txt'
assert output.read_bytes() == encoded
assert output.stat().st_size == len(encoded)
assert output.read_bytes() == encoded
report = {
    'status': 'passed',
    'scope': 'Exact text serialization, byte count, and coefficient-by-coefficient parse round trip; not a new arithmetic proof.',
    'source_sha256': hashlib.sha256(raw).hexdigest(),
    'text_sha256': hashlib.sha256(encoded).hexdigest(),
    'bytes': len(encoded),
    'bytes_if_one_LF_is_appended': len(encoded) + 1,
    'character_counts': counts,
    'variables': 250,
    'degree': 4,
    'nonzero_monomials': len(parsed),
    'implicit_unit_coefficients': sum(abs(c) == 1 and bool(m) for m, c in terms.items()),
    'round_trip_matches_every_coefficient': True,
    'encoding': 'ASCII, equivalently UTF-8 without BOM; no whitespace or trailing newline',
    'under_100000_bytes': len(encoded) < 100000,
    'under_102400_bytes': len(encoded) < 102400,
}
(ROOT.parents[3] / 'build/version19/plain-text-verification.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
print(json.dumps(report, indent=2))
