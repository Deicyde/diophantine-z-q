"""Import closure of a module on a git ref (reads files via git; no checkout).
Usage: python3 closure.py REF ROOTMODULE [ROOTMODULE...]  -> prints the closure (project modules only), one per line."""
import subprocess, sys, re
ref = sys.argv[1]; roots = sys.argv[2:]
files = subprocess.run(['git', 'ls-tree', '-r', '--name-only', ref], capture_output=True, text=True, check=True).stdout.split('\n')
lean = {f[:-5].replace('/', '.'): f for f in files if f.endswith('.lean')}
def imports(mod):
    src = subprocess.run(['git', 'show', f'{ref}:{lean[mod]}'], capture_output=True, text=True, check=True).stdout
    out = []
    for line in src.split('\n'):
        m = re.match(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(.*)$', line)
        if m:
            out += [x for x in m.group(1).split() if not x.startswith('--')]
    return out
seen = set(); stack = list(roots)
while stack:
    m = stack.pop()
    if m in seen or m not in lean: continue
    seen.add(m)
    stack += imports(m)
for m in sorted(seen): print(m)
