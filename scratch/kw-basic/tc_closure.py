"""Print the ZInQKernel.Contrib.TauCeti import closure of a module (repo-relative)."""
import re, sys
start = sys.argv[1]
seen, todo = set(), [start]
while todo:
    m = todo.pop()
    path = m.replace('.', '/') + '.lean'
    for line in open(path):
        mm = re.match(r'\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)', line)
        if mm and mm.group(1).startswith('ZInQKernel.') and mm.group(1) not in seen:
            seen.add(mm.group(1)); todo.append(mm.group(1))
for m in sorted(seen):
    print(m)
