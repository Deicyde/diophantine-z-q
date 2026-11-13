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
     ['RatFactorAlgClosed', 'ptOf', 'ratEval']),
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
sys.exit(0 if ok else 1)
