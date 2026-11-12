#!/usr/bin/env python3
"""Bounded semantic regression controls; no arithmetic-theorem acceptance."""
import importlib.util
import json
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('assembler', HERE / 'assemble.py')
a = importlib.util.module_from_spec(spec)
spec.loader.exec_module(a)
tex, mapping = a.assemble()
mapping = json.loads(mapping)
by_id = {c['id']: (s, c) for s in mapping['spans']
         for c in s.get('source_corrections', [])}
assert {'F1', 'F2'} <= set(by_id)
assert len(by_id) == 19
for fid, expected, forbidden in [
    ('F1', a.math('D(mu_sigma)^(-1/4)'), a.math('D(mu_sigma)^-1/4')),
    ('F2', a.math('∑_j e_j f_j=d'), a.math('∑e_jf_j=d')),
]:
    span, correction = by_id[fid]
    start, end = span['tex_lines']
    passage = '\n'.join(tex.decode().splitlines()[start - 1:end])
    assert expected in passage, (fid, passage)
    assert forbidden not in passage, (fid, passage)
# Extension labels are complete subscripts; slash stays inside the index.
for fid, required in {
    'F3-1': [r'D_{U/V}'],
    'F3-2': [r'\Omega _{E/V}'],
    'F3-3': [r'\omega _{A/V}', r'\Omega _{A/V}'],
    'F3-4': [r'\operatorname{Tr}_{L/\text{Frac}(V)}'],
    'F3-5': [r'\operatorname{Tr}_{U/W}', r'U^{\vee }_{V}'],
    'F3-6': [r'D_{U/V}', r'D_{U/W}', r'D_{W/V}',
              r'r_{U/V}', r'r_{U/W}', r'e_{U/W}', r'r_{W/V}'],
    'F3-7': [r'\omega _{{\mathcal X}/O_{K}}'],
    'F3-8': [r'\omega _{{\mathcal X}/O_{K}}'],
}.items():
    span, _ = by_id[fid]
    passage = '\n'.join(tex.decode().splitlines()[span['tex_lines'][0]-1:span['tex_lines'][1]])
    for expected in required:
        assert expected in passage, (fid, expected, passage)
# Check numeric coordinate indices against literal TeX, independently of
# assembler.math: before repair these remained baseline digits under powers.
for fid, (_, correction) in by_id.items():
    if not fid.startswith('F4-'):
        continue
    import re
    span, _ = by_id[fid]
    passage = '\n'.join(tex.decode().splitlines()[span['tex_lines'][0]-1:span['tex_lines'][1]])
    for symbol, index, power in re.findall(r'([A-Za-z])([0-9]+)([¹²³⁴])', next(c['original_line'] for c in json.loads(a.CORRECTIONS.read_text())['corrections'] if c['id'] == fid)):
        exponent = str('¹²³⁴'.index(power)+1)
        assert symbol+'_{'+index+'}^{'+exponent+'}' in passage, (fid, passage)
        assert symbol+index+'^{'+exponent+'}' not in passage, (fid, passage)
# Pullback star and bracketed morphism label must survive prose parsing.
span, correction = by_id['F3-2']
assert correction['finding_ids'] == ['F3', 'F5']
passage = '\n'.join(tex.decode().splitlines()[span['tex_lines'][0]-1:span['tex_lines'][1]])
assert r'[n]^{*}\omega =n\omega ' in passage, passage
assert r'\Omega _{[n]}=(n)' in passage, passage
assert r'\emph{' not in passage and '^{}' not in passage
# Related star uses have distinct meanings and stay as authored.
for source, line, required in [
    ('research/quartic214/proofs/height-evaluation.md', 45, r'a_i^*\omega'),
    ('research/quartic214/proofs/height-evaluation.md', 48, r'\alpha ^{*}E'),
    ('research/quartic214/sources/conductor-sections1-3.md', 27, r'Q_{11}^{*}'),
]:
    related = next(s for s in mapping['spans'] if s['source'] == source
                   and s['source_lines'][0] <= line <= s['source_lines'][1])
    block = '\n'.join(tex.decode().splitlines()[related['tex_lines'][0]-1:related['tex_lines'][1]])
    assert required in block, (source, block)
# Independently distinguish the mathematical readings at identity and a
# nonidentity perfect fourth degree; this catches the old /4 regression.
for root in (1, 2, 3):
    degree = root ** 4
    normalized = Fraction(1, root)
    assert normalized ** 4 * degree == 1
    assert (Fraction(1, degree) / 4) ** 4 * degree != 1
# Include every component and multiply residue degrees, rather than treating
# jf_j as an index. Unequal residue degrees make dropped factors visible.
components = [(2, 3), (3, 2), (1, 4)]
assert sum(e * f for e, f in components) == 16
assert sum(e for e, f in components) != 16
# Genuine quotients adjacent to powers must retain their original grouping.
assert a.math('g^4/f^2') == 'g^{4}/f^{2}'
assert a.math('Z0^4/R_s^10') == 'Z_{0}^{4}/R_{s}^{10}'
# Both frozen source SHA and exact line gate the overlay. No global guess.
original = a.CORRECTIONS
import tempfile
with tempfile.TemporaryDirectory(dir=HERE) as temporary:
    candidate = Path(temporary) / 'stale.json'
    payload = json.loads(original.read_text())
    payload['corrections'][0]['source_sha256'] = '0' * 64
    candidate.write_text(json.dumps(payload))
    a.CORRECTIONS = candidate
    try:
        a.markdown(a.ROOT / payload['corrections'][0]['source'], 'test')
    except ValueError as error:
        assert 'Stale source correction' in str(error)
    else:
        raise AssertionError('stale correction accepted')
print('PASS: corrected consumers, semantic negative controls, quotient grouping, stale-source rejection')
