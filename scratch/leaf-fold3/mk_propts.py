#!/usr/bin/env python3
"""leaf-fold3: part partsF/c80_propts.lean, Proposition TS from the merged prop-ts files.
All of these files begin with prop-ts's PropTS.lean body (verbatim) and continue with some version of
prop-ts-glue's appendix; their shared declarations are byte-identical (checked below). The part is:
  1. scratch/prop-ts/PropTS.lean lines 25-29 and 64-906 (its lines 30-63, fibre-cover's `PropTS` and
     `PropTSAll`, are part a70; as g0-assemble3's part e10);
  2. scratch/prop-ts-glue/PropTSGlue.lean (3d41b3d5, final: `specNonMeeting` proved) after the PropTS body;
  3. for kummer-comp/KummerComp.lean and hecke-rest/HeckeRestAll.lean in this order: the text after the
     PropTS body. KummerComp.lean contains the whole ts-kummer file it was built on (the current
     ts-kummer/KummerTS.lean has a forward reference, `kummerMeetGlue` before
     `kummerMeetGlue_of_compositum`, so it is not used separately).
  In every source, each declaration whose full name already occurs in the chain (LPrefix, parts/,
  partsF/c1*-c7*) or earlier in this part is dropped, with the `… in` modifiers that applied to it;
  the script prints the dropped names whose text differs.
  One name-resolution edit (REPL below): hecke-rest's `rw [bcPt, …]` becomes `rw [LeafQM.AV.bcPt, …]`.
  Declarations whose text is identical to one already present are also dropped.
  `set_option synthInstance.maxHeartbeats 400000` (kummer-comp's compositum core times out at the default
  with this chain's larger instance set). HeckeRestAll.lean contains the whole of the ts-hecke file it was built on
     (an earlier TSHecke.lean, whose `HeckeFibreSizes` has the extra clause `∀ P, #fibre ≤ M` that
     hecke-rest proves), so the current ts-hecke/TSHecke.lean is not used separately;
`#print`/`#check`/`import` lines dropped; leaf-fold's HDec edits as in mk_lf3.py.
ts-sn's TSSN.lean is not used: prop-ts-glue's final file already proves `SNSpecialize` and `specNonMeeting`."""
import sys, re
sys.path.insert(0, 'py')
from chunks import chunks, text, fullnames
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
            if (full in seen or text(c) in seen_text) and not keep_all:
                if full in seen and seen[full] != text(c): diffs.append(full)
                ndrop += 1
                # drop the `… in` modifiers (open/attribute/set_option/omit … in) that applied to it
                while out and re.match(r'^(open|attribute|set_option|omit|include|variable)\b.*\sin\s*$', out[-1]) and '\n' not in out[-1]:
                    out.pop()
                continue
            seen.setdefault(full, text(c)); seen_text.add(text(c))
        out.append(text(c))
    print(tag, 'dropped', ndrop, 'diff', diffs, file=sys.stderr)
    return '\n'.join(out), diffs
import glob
seen = {}
# the chain's declarations (LPrefix, parts/, partsF/ before c80): drop copies of them too
for f in ['olean/LPrefix.lean'] + sorted(glob.glob('parts/*.lean')) + sorted(p for p in glob.glob('partsF/c[1-7]*.lean')):
    for n, c in fullnames(chunks(open(f).read())):
        if isinstance(n, str) and n.startswith('HDec.'): n = n[5:]
        if isinstance(n, tuple) and n[1].startswith('HDec'): n = (n[0], n[1][5:], n[2])
        seen.setdefault(n, text(c))
seen_text = set(seen.values())
parts = []
pts, _ = walk(chunks('\n'.join(P[24:29]) + '\n' + '\n'.join(P[63:906])), seen, tag='PropTS')
parts.append(pts)
b, _ = walk(chunks(post('prop-ts-glue/PropTSGlue.lean')), seen, tag='PropTSGlue')
parts.append(b)
for f in ['kummer-comp/KummerComp.lean', 'hecke-rest/HeckeRestAll.lean']:
    t, d = walk(chunks(post(f)), seen, tag=f)
    parts.append('/-! ## leaf-fold3: %s after the PropTS body, declarations already above dropped -/\n\n' % f + t)
# one name-resolution edit: inside this chain both `LeafQM.AV.bcPt` (Leaves.lean) and `LeafQM.AV.Pin.bcPt`
# (part a56) are open in hecke-rest's `HeckeRest` namespace; its `rw [bcPt, …]` means the former
REPL = [('      rw [bcPt, ← MonObj.comp_pow, hx]', '      rw [LeafQM.AV.bcPt, ← MonObj.comp_pow, hx]')]
hdr0 = 'set_option synthInstance.maxHeartbeats 400000\n'
hdr = ('-- (leaf-fold3) mk_propts.py: prop-ts PropTS.lean (lines 25-29, 64-906), prop-ts-glue PropTSGlue.lean (after the PropTS body),\n'
       '-- then ts-kummer, kummer-comp, ts-hecke, hecke-rest (after the PropTS body, already-present declarations dropped)\n')
txt = '\n\n'.join(parts)
for a, b in REPL:
    assert txt.count(a) == 1, a
    txt = txt.replace(a, b)
open('partsF/c80_propts.lean', 'w').write(hdr + hdr0 + hdec(txt) + '\n')
print('ok')
