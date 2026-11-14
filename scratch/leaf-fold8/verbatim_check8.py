#!/usr/bin/env python3
"""leaf-fold8: check the generated modules against their sources (run from the repository root).

For each generated module: every line of the source slice, minus `#print` lines, appears in the module, unchanged
and in order, and the module's extra lines are only its header (imports, banner docstring, `set_option linter.all
false`). For TailZ2 also: lines 37-2197 of `HauptGlue.lean` (leafq-check's `Fold.lean` part, replaced by the import
of `TailO`) occur in `TailO.lean` in order and as contiguous blocks."""
import sys

def lines(f):
    return open(f).read().split('\n')

ok = True
def check(mod, src, a, b):
    global ok
    M = lines('ZInQKernel/OneProof/' + mod)
    S = [l for l in lines(src)[a - 1:b] if not l.startswith('#print')]
    while S and S[-1].strip() == '':
        S.pop()
    # find the start of the copied body: the first line of S in M after the header
    while S and S[0].strip() == '':
        S.pop(0)
    i = next((k for k in range(len(M)) if M[k:k + len(S)] == S), M.index(S[0]))
    body = M[i:i + len(S)]
    same = body == S
    extra = M[i + len(S):]
    tail_ok = all(l.strip() == '' for l in extra)
    print(f'{mod}: {len(S)} source lines, verbatim block {"OK" if same else "DIFFERS"}, '
          f'header {i} lines, trailing extra {"none" if tail_ok else len(extra)}')
    if not same:
        for k, (x, y) in enumerate(zip(body, S)):
            if x != y:
                print('  first difference at module line', i + k + 1, repr(x[:80]), repr(y[:80]))
                break
        ok = False
    ok = ok and tail_ok

check('H/TailY.lean', 'scratch/height-glue/Rows.lean', 10, 2011)
check('H/TailZ.lean', 'scratch/height-glue/Rows.lean', 2012, 10 ** 6)
check('H/TailZ2.lean', 'scratch/qm-glue/HauptGlue.lean', 2198, 3687)
check('H/TailZ3.lean', 'scratch/qm-glue/HauptGlue.lean', 3688, 10 ** 6)
check('TYZSplit.lean', 'scratch/tyz-split/T11.lean', 2, 10 ** 6)

# HauptGlue lines 37-2197 inside TailO, in order, as contiguous blocks
H = lines('scratch/qm-glue/HauptGlue.lean')[36:2197]
O = lines('ZInQKernel/OneProof/H/TailO.lean')
j, blocks, cur = 0, [], None
for k, l in enumerate(H):
    if cur is not None and j < len(O) and O[j] == l:
        j += 1
        continue
    # start a new block: find l at or after j
    while j < len(O) and O[j] != l:
        j += 1
    if j == len(O):
        print('HauptGlue line', k + 37, 'not found in TailO:', repr(l[:80]))
        ok = False
        break
    blocks.append((k + 37, j + 1))
    cur = j
    j += 1
print(f'HauptGlue 37-2197 in TailO: {len(blocks)} contiguous blocks starting at (HauptGlue line, TailO line):',
      blocks[:10])
print('ALL OK' if ok else 'FAILED')
sys.exit(0 if ok else 1)
