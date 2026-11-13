"""Remove declarations unreachable from the three roots (Dead.lean output dead.out) from
ZInQKernel/Contrib/Mobius/*.lean. A dead declaration is kept if its range lies inside a used
declaration's range (generated lemmas) or if its last name component occurs textually in the
remaining code (fixpoint). A preceding `open ... in` line goes with a removed declaration."""
import re, pathlib, collections
root = pathlib.Path(__file__).resolve().parents[2]
decls = collections.defaultdict(list)
for line in (root / 'scratch/mobius-contrib/dead.out').read_text().splitlines():
    m = re.search(r'DECL (USED|DEAD) ZInQKernel\.Contrib\.Mobius\.(\w+) (\d+) (\d+) (\S+)', line)
    if m:
        decls[m[2]].append((m[1], int(m[3]), int(m[4]), m[5]))
files = {mod: (root / f'ZInQKernel/Contrib/Mobius/{mod}.lean').read_text().split('\n') for mod in decls}
dead = {}
for mod, ds in decls.items():
    used = [(a, b) for k, a, b, _ in ds if k == 'USED']
    for k, a, b, n in ds:
        if k == 'DEAD' and not any(ua <= a and b <= ub for ua, ub in used):
            dead[(mod, n)] = (a, b)
def short(n): return n.split('.')[-1]
while True:
    removed = {mod: set() for mod in files}
    for (mod, n), (a, b) in dead.items():
        removed[mod] |= set(range(a, b + 1))
    remaining = '\n'.join(l for mod, ls in files.items() for i, l in enumerate(ls, 1) if i not in removed[mod])
    keep = [k for k in dead if re.search(r'(?<![\w.])(\w+\.)*' + re.escape(short(k[1])) + r'(?![\w\'])', remaining)]
    if not keep: break
    for k in keep:
        print('kept (textual use):', k)
        del dead[k]
for mod, ls in files.items():
    rm = set()
    for (m, n), (a, b) in dead.items():
        if m != mod: continue
        rm |= set(range(a, b + 1))
        if a >= 2 and re.match(r'^open .* in$', ls[a - 2]): rm.add(a - 1)
    out, prev_blank = [], False
    for i, l in enumerate(ls, 1):
        if i in rm: continue
        blank = (l.strip() == '')
        if blank and prev_blank: continue
        out.append(l); prev_blank = blank
    (root / f'ZInQKernel/Contrib/Mobius/{mod}.lean').write_text('\n'.join(out))
    print(mod, 'removed', len([1 for (m, _) in dead if m == mod]), 'decls,', len(ls), '->', len(out), 'lines')
for (m, n) in sorted(dead): print('REMOVED', m, n)
