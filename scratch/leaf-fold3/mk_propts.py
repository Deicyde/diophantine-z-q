#!/usr/bin/env python3
"""leaf-fold3: part partsF/c80_propts.lean, Proposition TS from the merged prop-ts files.
All of these files begin with prop-ts's PropTS.lean body (verbatim) and continue with some version of
prop-ts-glue's appendix; their shared declarations are byte-identical (checked below). The part is:
  1. scratch/prop-ts/PropTS.lean lines 25-29 and 64-906 (its lines 30-63, fibre-cover's `PropTS` and
     `PropTSAll`, are part a70; as g0-assemble3's part e10);
  2. scratch/prop-ts-glue/PropTSGlue.lean (3d41b3d5, final: `specNonMeeting` proved) after the PropTS body;
  3. for ts-kummer/KummerTS.lean, kummer-comp/KummerComp.lean and hecke-rest/HeckeRestAll.lean in this
     order: the text after the PropTS body, with every declaration whose full name already occurs above
     dropped (the script prints the dropped names whose text differs: two docstrings of ts-kummer,
     re-worded by kummer-comp). HeckeRestAll.lean contains the whole of the ts-hecke file it was built on
     (an earlier TSHecke.lean, whose `HeckeFibreSizes` has the extra clause `∀ P, #fibre ≤ M` that
     hecke-rest proves), so the current ts-hecke/TSHecke.lean is not used separately;
`#print`/`#check`/`import` lines dropped; leaf-fold's HDec edits as in mk_lf3.py.
ts-sn's TSSN.lean is not used: prop-ts-glue's final file already proves `SNSpecialize` and `specNonMeeting`."""
import sys, re
sys.path.insert(0, 'py')
from chunks import chunks, text
sys.path.insert(0, '.')
from mk_lf3 import hdec  # noqa
R = '../'
P = open(R + 'prop-ts/PropTS.lean').read().split('\n')
body = '\n'.join(P[24:])
def post(f):
    s = open(R + f).read(); i = s.find(body); assert i >= 0, f
    return s[i + len(body):]
def walk(cs, seen, keep_all=False, tag=''):
    ns = []; out = []; ndrop = 0; diffs = []
    for c in cs:
        if c['kind'] == 'struct':
            l = c['lines'][0]
            if l.startswith('namespace '): ns.append(('n', l.split()[1]))
            elif l.startswith('section'): ns.append(('s', l.split()[1] if len(l.split()) > 1 else ''))
            elif l.startswith('noncomputable section'): ns.append(('s', ''))
            elif l.startswith('end'):
                if ns: ns.pop()
            if l.startswith('#') or l.startswith('import '): continue
            out.append(text(c)); continue
        if c['kind'] == 'decl' and c['name']:
            nm = c['name']
            full = '.'.join([x[1] for x in ns if x[0] == 'n'] + [nm])
            if full in seen and not keep_all:
                if seen[full] != text(c): diffs.append(full)
                ndrop += 1; continue
            seen.setdefault(full, text(c))
        out.append(text(c))
    print(tag, 'dropped', ndrop, 'diff', diffs, file=sys.stderr)
    return '\n'.join(out), diffs
seen = {}
parts = []
parts.append('\n'.join(P[24:29]) + '\n' + '\n'.join(P[63:906]))
walk(chunks(body), seen, keep_all=True, tag='PropTS')
b, _ = walk(chunks(post('prop-ts-glue/PropTSGlue.lean')), seen, keep_all=True, tag='PropTSGlue')
parts.append(b)
for f in ['ts-kummer/KummerTS.lean', 'kummer-comp/KummerComp.lean', 'hecke-rest/HeckeRestAll.lean']:
    t, d = walk(chunks(post(f)), seen, tag=f)
    parts.append('/-! ## leaf-fold3: %s after the PropTS body, declarations already above dropped -/\n\n' % f + t)
hdr = ('-- (leaf-fold3) mk_propts.py: prop-ts PropTS.lean (lines 25-29, 64-906), prop-ts-glue PropTSGlue.lean (after the PropTS body),\n'
       '-- then ts-kummer, kummer-comp, ts-hecke, hecke-rest (after the PropTS body, already-present declarations dropped)\n')
open('partsF/c80_propts.lean', 'w').write(hdr + hdec('\n\n'.join(parts)) + '\n')
print('ok')
