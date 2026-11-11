# Apply research/version16 EDITS.json, EDITORIAL-AMENDMENT.json (if textual) and TZ-PRECISION-AMENDMENT.json
# to the Version 15 source and compare with quartic_v16.tex. Reads upstream files only.
import json, hashlib, sys, os
U = os.path.expanduser('~/upstream')
rd = lambda p: open(os.path.join(U, p), encoding='utf8', newline='').read()
E = json.load(open(os.path.join(U, 'research/version16/EDITS.json')))
src = rd(E['baseline'])
print('baseline sha ok:', hashlib.sha256(src.encode()).hexdigest() == E['baseline_sha256'])
for e in E['edits']:
    n = src.count(e['old']); assert n == 1, (e['id'], n)
    src = src.replace(e['old'], e['new'])
print('after EDITS sha matches EDITS.sha256:', hashlib.sha256(src.encode()).hexdigest() == E['sha256'])
ed = json.load(open(os.path.join(U, 'research/version16/EDITORIAL-AMENDMENT.json')))
print('editorial keys:', list(ed)[:12])
for k in ('edits', 'replacements'):
    for e in ed.get(k, []):
        o, nw = e.get('old', e.get('before')), e.get('new', e.get('after'))
        assert src.count(o) == 1, e.get('id'); src = src.replace(o, nw)
if 'before' in ed and 'after' in ed:
    assert src.count(ed['before']) == 1; src = src.replace(ed['before'], ed['after'])
tz = json.load(open(os.path.join(U, 'research/version16/TZ-PRECISION-AMENDMENT.json')))
b, a = tz['before'], tz['after']
if src.count(b) != 1:
    b, a = b.replace('\n', '\r\n'), a.replace('\n', '\r\n')
assert src.count(b) == 1; src = src.replace(b, a)
v16 = rd('manuscripts/quartic_v16.tex')
print('reconstructed == quartic_v16.tex:', src == v16)
if src != v16:
    import difflib
    for l in list(difflib.unified_diff(src.splitlines(), v16.splitlines(), lineterm='', n=0))[:40]: print(l[:200])
