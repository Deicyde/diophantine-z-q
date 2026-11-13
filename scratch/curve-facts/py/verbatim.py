"""Check that the copied declarations are textually identical to the source."""
import re, sys
src = open('scratch/mobius-glue/MobiusGlue.lean').read()
dst = open('scratch/curve-facts/CurveFacts.lean').read()
def decl(text, head):
    i = text.index(head)
    # back up to the docstring start if any
    j = text.rfind('/--', 0, i)
    k = text.rfind('-/', 0, i)
    start = j if j != -1 and text[k+2:i].strip() in ('', 'open Polynomial in', 'open scoped Classical in') else i
    m = re.search(r'\n\n', text[i:])
    return text[start:i + m.start()]
ok = True
for head in ['def CurveRatFactor', 'def CurveSurj', 'def ratEval']:
    a, b = decl(src, head), decl(dst, head)
    print(head, 'IDENTICAL' if a == b else 'DIFFERENT')
    ok &= a == b
sys.exit(0 if ok else 1)
