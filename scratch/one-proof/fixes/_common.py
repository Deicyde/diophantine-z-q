"""Generic fixes applied to every regenerated H module (op-dedupe): dot notation on the kernel's `PkgI4.GaloisRep`
for HDec predicates (the field lookup goes to the kernel namespace, where these do not exist)."""
import re, sys
F = sys.argv[1]
s = open(F).read()
n = 0
for pred in ['HasHTWeightsAtSelf', 'DistinctHTWeights']:
    s, k = re.subn(r"(?<![\w.'`])([ρr][\w']*)\." + pred + r"\b", r"PkgI4.GaloisRep." + pred + r" (ρ := \1)", s)
    n += k
open(F, 'w').write(s)
print('common fixes:', n)
