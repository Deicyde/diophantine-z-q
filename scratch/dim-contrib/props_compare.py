"""Compare the named Props of ZInQKernel/Contrib/Dim/ with curve-infra's (scratch/curve-infra/CurveInfraAll.lean).
Allowed differences: fnFieldAlgebra -> functionFieldAlgebra."""
import re, glob
def defs(text):
    out = {}
    for m in re.finditer(r'^def (\w+) : Prop :=\n((?:  .*\n)+)', text, re.M):
        out[m.group(1)] = m.group(2)
    return out
old = defs(open('scratch/curve-infra/CurveInfraAll.lean').read())
new = {}
for f in sorted(glob.glob('ZInQKernel/Contrib/Dim/*.lean')):
    new.update(defs(open(f).read()))
for k, v in old.items():
    nv = new.get(k)
    if nv is None: print(k, 'MISSING'); continue
    ov = v.replace('fnFieldAlgebra', 'functionFieldAlgebra')
    print(k, 'IDENTICAL (modulo fnFieldAlgebra->functionFieldAlgebra)' if ov == nv else 'DIFFERENT')
