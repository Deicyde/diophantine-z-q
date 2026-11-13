#!/usr/bin/env python3
"""leaf-adopt3: for each folded task, compare its declarations (as in scratch/<task>/) with the
same-named declarations of the new Leaves.lean (statement text for theorems, full text for defs,
comments stripped). Prints, per task, how many matched, differ, or were not copied."""
import sys, importlib.util, glob
spec = importlib.util.spec_from_file_location('sd', 'scratch/leaf-adopt3/stmt_diff.py')
src = open('scratch/leaf-adopt3/stmt_diff.py').read().split('base = subprocess.run')[0]
ns = {}; exec(src, ns); decls = ns['decls']
new = decls(open('scratch/h-decomposition/Leaves.lean').read())
tasks = {'t-skolem-kw': ['SkolemNoether', 'BrauerNesbitt', 'FrobeniusDense', 'KroneckerWeberUse', 'C10Closed'],
         't-different': ['All'], 't30-adelic': ['SqrtCrit'], 't10-etale': ['T10Etale'], 'pi0-x6': ['Pi0X6'],
         'hodge-lattice': ['HodgeLattice'], 'h5-neron': ['H5Neron'], 'x1-belyi': ['X1Belyi'],
         'e1-sub': ['E1Sub'], 'c9-rhof': ['C9'], 'g0-split': ['part_split']}
for t, files in tasks.items():
    S = {}
    for f in files:
        S.update(decls(open(f'scratch/{t}/{f}.lean').read()))
    same = [n for n in S if n in new and S[n] == new[n]]
    diff = [n for n in S if n in new and S[n] != new[n]]
    miss = [n for n in S if n not in new]
    print(f'{t}: {len(S)} decls; identical {len(same)}; differ {len(diff)}; not in Leaves.lean {len(miss)}')
    for n in diff: print('   DIFF', n)
    if len(miss) <= 40:
        for n in miss: print('   MISSING', n)
