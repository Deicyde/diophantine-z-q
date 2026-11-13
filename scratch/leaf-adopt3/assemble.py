#!/usr/bin/env python3
"""leaf-adopt3: assemble Leaves.lean = prefix (Leaves.orig.lean lines 1-21087) + parts/*.lean.
Usage: assemble.py tail   -> scratch/leaf-adopt3/olean/Tail.lean (import HDPrefix + parts)
       assemble.py full   -> scratch/h-decomposition/Leaves.lean
Fold fragments: parts/40_*.lean (between `end HSyn` and the reopened HSyn of the bundles)."""
import sys, glob, os
D = os.path.dirname(os.path.abspath(__file__))
parts = sorted(glob.glob(os.path.join(D, 'parts', '*.lean')))
body = []
for p in parts:
    name = os.path.basename(p)
    body.append(open(p).read().rstrip('\n') + '\n')
    if name.startswith('20_'):
        body.append('\nend HSyn\n\nend\n\n')
    if name.startswith('5'):  # 50_reopen marker handled by file
        pass
text = '\n'.join(body)
mode = sys.argv[1]
if mode == 'tail':
    open(os.path.join(D, 'olean', 'Tail.lean'), 'w').write('import HDPrefix\n\n' + text)
else:
    import subprocess
    orig = subprocess.run(['git', 'show', '883c4ddf:scratch/h-decomposition/Leaves.lean'],
                          capture_output=True, text=True, check=True, cwd=D).stdout
    pre = orig.split('\n')[:21087]
    out = os.path.join(D, '..', 'h-decomposition', 'Leaves.lean')
    open(out, 'w').write('\n'.join(pre) + '\n' + text)
    subprocess.run([sys.executable, os.path.join(D, 'header_edits.py'), out], check=True)
    subprocess.run([sys.executable, os.path.join(D, 'apply_repairs.py'), out], check=True)
