#!/usr/bin/env python3
"""leaf-fold5: part parts/e10_vertmodel.lean = vert-witness's VertMain.lean.part followed by model-glue's
ModelGlue.lean.part ... ModelGlue6.lean.part (in that order: model-glue's ModelGlue6.lean is
VertWitness.lean + these parts), ported into the chain's `namespace HDec` as leaf-fold3/4 ported hecke-rest:
  * `#print`/`#check`/`import` lines dropped, leaf-fold's `hdec` edits (`open ZInQ` -> `open _root_.ZInQ ZInQ`);
  * declarations whose full name already occurs in the chain (leaf-fold4's olean/*.lean sources) are dropped
    (the script prints them and whether their text differs);
  * EDITS below (each asserted to occur once)."""
import re, sys, glob
sys.path.insert(0, 'py')
from chunks import chunks, text, fullnames
R = '../'
def hdec(s):
    s = s.replace('_root_.PkgI4', '_root_.HDec.PkgI4')
    out = []
    for l in s.split('\n'):
        if l.startswith('#print') or l.startswith('#check') or l.startswith('import '):
            continue
        if l.startswith('open ') and re.search(r'(?<![\w.])ZInQ(?=\s|$)', l):
            l = re.sub(r'(?<![\w.])ZInQ(?=\s|$)', '_root_.ZInQ ZInQ', l, count=1)
        out.append(l)
    return '\n'.join(out)
seen = {}
for f in sorted(glob.glob(R + 'leaf-fold4/olean/*.lean')):
    if f.endswith(('Check3.lean', 'Check4.lean', 'Deps3.lean', 'FlatTailTest.lean', 'T1.lean', 'LF2ImagePlane.lean')): continue
    for n, c in fullnames(chunks(open(f).read())):
        if isinstance(n, str) and n.startswith('HDec.'): n = n[5:]
        if isinstance(n, str): seen.setdefault(n, text(c))
def walk(cs):
    ns = []; out = []; drops = []
    for c in cs:
        if c['kind'] == 'struct':
            l = c['lines'][0]
            if l.startswith('namespace '): ns.append(('n', l.split()[1]))
            elif l.startswith('section'): ns.append(('s', ''))
            elif l.startswith('noncomputable section'): ns.append(('s', ''))
            elif l.startswith('end'):
                if ns: ns.pop()
            if l.startswith('#') or l.startswith('import '): continue
            out.append(text(c)); continue
        if c['kind'] == 'decl' and c['name']:
            full = '.'.join([x[1] for x in ns if x[0] == 'n'] + [c['name']])
            if full in seen:
                drops.append((full, seen[full] == text(c)))
                while out and re.match(r'^(open|attribute|set_option|omit|include|variable)\b.*\sin\s*$', out[-1]) and '\n' not in out[-1]:
                    out.pop()
                continue
            seen[full] = text(c)
        out.append(text(c))
    return '\n'.join(out), drops
srcs = ['vert-witness/VertMain.lean.part'] + ['model-glue/ModelGlue%s.lean.part' % s for s in ['', '2', '3', '4', '5', '6']]
parts = []
for f in srcs:
    t, d = walk(chunks(open(R + f).read()))
    print(f, 'dropped', d, file=sys.stderr)
    parts.append('/-! ## leaf-fold5: scratch/%s (declarations already in the chain dropped) -/\n\n' % f + t)
txt = '\n\n'.join(parts)
EDITS = [
 # (c) the kernel's proof of SmoothFibreReduced (ZInQKernel/Contrib/SmoothFibre/Basic.lean, imported): its statement
 # is over Mathlib only and has the same text as vert-witness's `SmoothFibreReduced`
 (open(R + 'model-glue/ModelGlue6.lean.part').read().split('\n\n/-- **The two targets')[0].split('/-- **`SmoothFibreReduced`, proved**')[1],
  " (the kernel's `ZInQ.SmoothFibre.smoothFibreReduced`, leaf-fold5). -/\ntheorem smoothFibreReduced' : SmoothFibreReduced :=\n  _root_.ZInQ.SmoothFibre.smoothFibreReduced"),

]
EDITS.append((
 # (c) the kernel's lemma (ZInQKernel/Contrib/SmoothFibre/Basic.lean, imported), of which model-glue's is a copy
 open(R + 'model-glue/ModelGlue4.lean.part').read().split('theorem isReduced_of_etale_of_isDomain\' ')[1].split('\n\n')[0],
 "(P S : Type*) [CommRing P] [IsDomain P] [CommRing S]\n    [Algebra P S] [Algebra.Etale P S] : IsReduced S :=\n  _root_.ZInQ.SmoothFibre.isReduced_of_etale_of_isDomain P S"))
EDITS.append(("An étale algebra over a domain is reduced (copied verbatim from task smooth-fibre,",
 "An étale algebra over a domain is reduced (leaf-fold5: the kernel's lemma, of which model-glue had a verbatim copy,"))
# the kernel's proved curve facts (LeafQM.AV.Pin.curveFacts, smoothStalkDimOne, over the kernel's ToP1) are not the
# chain's constants; the chain's own are leaf-fold3's `HSyn.smoothStalkDimOne_proved` and the curve facts from
# `curveFacts_of_leaves` with the three `_proved` theorems of part b20 (themselves the kernel's theorems through `toP1K`)
txt = txt.replace('curveFacts.2 S hprop hsm', 'HSyn.curveFacts5.2 S hprop hsm').replace('curveFacts.1 S hprop hsm', 'HSyn.curveFacts5.1 S hprop hsm')
txt = txt.replace('smoothCurveNoIsolatedPoint_of smoothStalkDimOne ℚ', 'smoothCurveNoIsolatedPoint_of HSyn.smoothStalkDimOne_proved ℚ')
PRE = """noncomputable section

namespace HSyn

/-- The curve facts in the chain's own terms (leaf-fold3's `mobiusGlue_of_t5'` uses the same term). -/
theorem curveFacts5 : LeafQM.AV.Pin.CurveRatFactor ∧ LeafQM.AV.Pin.CurveSurj :=
  LeafQM.AV.Pin.curveFacts_of_leaves smoothStalkDimOne_proved constOrOntoAlgClosed_proved
    ratFactorAlgClosed_proved

end HSyn

end

"""
txt = PRE + txt
for a, b in EDITS:
    assert txt.count(a) == 1, a
    txt = txt.replace(a, b)
hdr = '-- (leaf-fold5) mk_e10.py: vert-witness VertMain.lean.part + model-glue ModelGlue{,2,...,6}.lean.part, in namespace HDec\n'
open('parts/e10_vertmodel.lean', 'w').write(hdr + hdec(txt) + '\n')
print('ok', txt.count('\n'))
