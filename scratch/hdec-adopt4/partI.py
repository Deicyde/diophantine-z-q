# Check that leaf-push2's Part I (up to `end ModelsSec`) is a copy of the adopted Faltings modules:
# every non-blank line, with `LeafPush2` renamed `DefFaltings`, appears in order in the
# concatenation of Faltings/{HodgeData,IdealLines,Models,Height}.lean (subsequence test), and
# every top-level declaration has the same whitespace-normalized block.
import re, sys
sys.path.insert(0, 'scratch/hdec-adopt2')
from decls import decls
from blocks import norm
L = open('scratch/leaf-push2/LeafPush2.lean').read().splitlines()
end = max(i for i, l in enumerate(L) if l.startswith('end ModelsSec'))
P = [l.replace('LeafPush2', 'DefFaltings') for l in L[18:end + 1] if l.strip()]
F = []
for m in ('HodgeData', 'IdealLines', 'Models', 'Height', 'Leaves'):
    F += [l for l in open(f'ZInQKernel/HDecomp/Faltings/{m}.lean').read().splitlines() if l.strip()]
j = 0; miss = []
for l in P:
    k = j
    while k < len(F) and F[k] != l: k += 1
    if k == len(F): miss.append(l)
    else: j = k + 1
print('Part I non-blank lines', len(P), 'not found in order:', len(miss))
for l in miss: print('  MISS', l[:98])
