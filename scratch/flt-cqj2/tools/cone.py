import sys, os, re, json
root = sys.argv[1]; start = sys.argv[2:]
def path(m): return os.path.join(root, m.replace('.', '/') + '.lean')
seen = {}; stack = list(start)
while stack:
    m = stack.pop()
    if m in seen: continue
    p = path(m)
    if not os.path.exists(p): seen[m] = None; continue
    imps = []
    for line in open(p, encoding='utf-8'):
        mm = re.match(r'^import\s+(\S+)', line)
        if mm: imps.append(mm.group(1))
        elif line.strip() and not line.startswith('import'): 
            if not line.startswith('--'): break
    imps = [i for i in imps if not i.startswith('Mathlib')]
    seen[m] = imps; stack += imps
json.dump(seen, sys.stdout, indent=0)
