"""Check that declarations copied into scratch/curve-glue are textually identical to their sources
(docstring included). Usage: python3 -I scratch/curve-glue/py/verbatim.py (from the repo root)."""
import re, sys

def decl(text, name):
    """Return the text of declaration `name`: its preceding docstring (if any) through the line
    before the next blank-line-separated top-level item."""
    m = re.search(r'(?m)^(?:noncomputable )?(?:def|abbrev|theorem) ' + re.escape(name) + r'\b', text)
    if not m:
        return None
    start = m.start()
    # include an immediately preceding docstring (and `open ... in` lines)
    pre = text[:start]
    k = pre.rfind('/--')
    if k != -1 and pre[k:].count('-/') == 1 and pre[k:].rstrip().endswith('-/') or (k != -1 and re.fullmatch(r'(?s)/--.*?-/\s*(open .* in\s*)?', pre[k:])):
        start = k
    end = text.find('\n\n', m.end())
    return text[start:end if end != -1 else len(text)]

checks = [
    ('scratch/curve-glue/C2K.lean', 'scratch/curve-facts/CurveFacts.lean',
     ['ConstOrOntoAlgClosed', 'RatFactorAlgClosed', 'ptOf', 'ratEval',
      'isOpen_connectedComponent_of_noetherian']),
    ('scratch/curve-glue/C3K.lean', 'scratch/curve-facts/CurveFacts.lean',
     ['ConstOrOntoAlgClosed', 'RatFactorAlgClosed', 'ptOf', 'ratEval']),
    ('scratch/curve-glue/CMPoints.lean', 'scratch/h-decomposition/Leaves.lean',
     ['R1pi0Props', 'R2X6PropsIff', 'cmExists_of_iff', 'r2X6Props_of_iff']),
]
ok = True
for mine, src, names in checks:
    a, b = open(mine).read(), open(src).read()
    for n in names:
        x, y = decl(a, n), decl(b, n)
        same = x is not None and x == y
        ok &= same
        print(('IDENTICAL ' if same else 'DIFFERENT ') + f'{n:45s} {mine} vs {src}')
# R1R2fpRep: statement only (docstring abridged on purpose)
a = open('scratch/curve-glue/CMPoints.lean').read(); b = open('scratch/h-decomposition/Leaves.lean').read()
def stmt(t, n):
    m = re.search(r'(?m)^def ' + n + r'\b', t); e = t.find('\n\n', m.end()); return t[m.start():e]
s = stmt(a, 'R1R2fpRep') == stmt(b, 'R1R2fpRep'); ok &= s
print(('IDENTICAL ' if s else 'DIFFERENT ') + 'R1R2fpRep (statement; docstring abridged)')
# R1R2fp_of_rep: proof identical
s = stmt(a.replace('theorem R1R2fp_of_rep', 'def R1R2fp_of_rep'), 'R1R2fp_of_rep') == stmt(b.replace('theorem R1R2fp_of_rep', 'def R1R2fp_of_rep'), 'R1R2fp_of_rep'); ok &= s
print(('IDENTICAL ' if s else 'DIFFERENT ') + 'R1R2fp_of_rep (statement and proof; docstring abridged)')
# CurveGlueAll: prefix is CurveFacts.lean verbatim
cf = open('scratch/curve-facts/CurveFacts.lean').read(); al = open('scratch/curve-glue/CurveGlueAll.lean').read()
body = cf[cf.index('/-!'):cf.index('end Pin\n\nend AV\n\nend LeafQM\n\nend\n')]
s = body in al; ok &= s
print(('IDENTICAL ' if s else 'DIFFERENT ') + 'CurveGlueAll.lean contains CurveFacts.lean (header to end of §8) verbatim')
# MobiusEnd: mobius-glue §1-§5 (one destructuring line changed) and §7-§8 verbatim
mg = open('scratch/mobius-glue/MobiusGlue.lean').read(); me = open('scratch/curve-glue/MobiusEnd.lean').read()
i1 = mg.index('/-! ## §1 Rational functions on `P¹`'); i6 = mg.index('/-! ## §6 Downstream')
p1 = mg[i1:i6].replace("  obtain ⟨⟨hprop', hsmooth', hne', -, -⟩, -⟩ := h1'", "  obtain ⟨hprop', hsmooth', hne', -, -, -⟩ := h1'")
ie = mg.index('end Pin\n\nend AV\n\nend LeafQM\n', i6); isc = mg.index('/-- **The comparison of two triples from the curve facts and T5.** -/')
for lab, part in [('MobiusEnd.lean: mobius-glue §1-§5 verbatim except the h1\' destructuring line', p1),
                  ('MobiusEnd.lean: mobius-glue §7-§8 verbatim', mg[ie:isc])]:
    s_ = part in me; ok &= s_
    print(('IDENTICAL ' if s_ else 'DIFFERENT ') + lab)
cg = open('scratch/curve-glue/CurveGlueAll.lean').read()
j1 = cg.index('/-! ## §1 Geometric components (genuine definitions) -/'); je = cg.index('end Pin\n\nend AV\n\nend LeafQM\n\nend\n')
s_ = cg[j1:je] in me; ok &= s_
print(('IDENTICAL ' if s_ else 'DIFFERENT ') + 'MobiusEnd.lean: CurveGlueAll.lean §1 to the end verbatim')
# L0.lean: res, cst, GlobalFunctionsConst copied from C2K.lean
c2 = open('scratch/curve-glue/C2K.lean').read(); l0 = open('scratch/curve-glue/L0.lean').read()
for a, b in [("/-- Restriction of sections along", "/-- The value `s(p)"), ("/-- The constant section", "theorem ev_cst"),
             ("/-- **(L) \"Liouville\"", "section Main")]:
    i = c2.index(a); blk = c2[i:c2.index(b, i)]; s_ = blk in l0; ok &= s_
    print(('IDENTICAL ' if s_ else 'DIFFERENT ') + 'L0.lean copy of C2K block starting ' + a[:40])
# MobiusFinal: infra-smooth-dim §0-§4 and the proof of smoothStalkDimOne verbatim; L0 block verbatim
inf = open('scratch/infra-smooth-dim/SmoothDimProps.lean').read(); mf = open('scratch/curve-glue/MobiusFinal.lean').read()
a = inf.index('open Ideal IsLocalRing\n\nnamespace InfraSmoothDim'); b = inf.index('/-! ## §5 The glue Props')
p0 = inf.index('/-- **`SmoothStalkDimOne` holds**'); p1 = inf.index('end Pin', p0)
blk = l0[l0.index('/-! ## The leaf (L0) and the reduction -/'):l0.index('end Pin\n\nend AV')]
for lab, part in [('MobiusFinal: infra-smooth-dim §0-§4', inf[a:b]), ('MobiusFinal: smoothStalkDimOne proof', inf[p0:p1]),
                  ('MobiusFinal: L0.lean reduction block', blk), ('MobiusFinal: MobiusEnd body (from first section)', None)]:
    if part is None:
        me = open('scratch/curve-glue/MobiusEnd.lean').read(); k = me.index('/-! (curve-glue: §0 of mobius-glue dropped'); j = me.index('/-- **The kernel\'s `MobiusGlue` from C1b')
        part = me[k:j]
    s_ = part in mf; ok &= s_
    print(('IDENTICAL ' if s_ else 'DIFFERENT ') + lab)
sys.exit(0 if ok else 1)
