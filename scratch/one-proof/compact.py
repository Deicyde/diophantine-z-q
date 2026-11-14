"""op-compact: replace op-dedupe's repeated alias opens by `export` aliases at the deleted copies' names.

For each H module M (import order), the tagged lines `open _root_.Q (r ...) -- op-dedupe` alias `r` to the
kernel's `Q.r`, where `HDec.Q.r` was a deleted copy. This script removes these lines and puts, once, after M's
imports, for each top component T of the names first aliased in M:
    namespace HDec.T export _root_.T (rest ...) end HDec.T
which re-creates `HDec.T.rest` as an alias of the kernel's `T.rest`, so every reference resolves as it did to the
copy. The tagged lines that replace an original explicit-list open (below a `-- op-dedupe was:` comment)
are kept. Names aliased by an earlier module are not repeated (aliases persist through imports).
Usage: compact.py REPO [--dry]
"""
import re, sys, pathlib
repo = pathlib.Path(sys.argv[1]); dry = '--dry' in sys.argv
ORDER = 'LPrefix TailA TailB TailC TailD LF2Stalks LF2UnifRoot LF2SmoothDim LF2UnramConj LF3Cot TailE TailF TailG TailH TailI LF4T5 TailJ TailK'.split()
TAGRE = re.compile(r'^\s*open _root_\.(\S+) \(([^)]*)\)( in)? -- op-dedupe$')
# the constants below each target (fields, constructors, `X.lemma`): an alias, unlike an explicit open, does not
# reach `x.y` from `x`, so they are aliased too (scratch/one-proof/Children.lean writes export_children.txt)
# A child is aliased in the first module (not before its target's) whose imports reach the child's module.
def srcfile(m):
    for root in (repo, repo / 'lean'):
        f = root / (m.replace('.', '/') + '.lean')
        if f.exists(): return f
    return None
closure = {}
def reach(m):
    if m in closure: return closure[m]
    closure[m] = {m}; f = srcfile(m)
    if f:
        for l in f.read_text(encoding='utf-8').split('\n'):
            if l.startswith('import '):
                for x in l.split()[1:]: closure[m] |= reach(x)
    return closure[m]
kids = {}  # target -> [(child, module)]
cf = repo / 'scratch/one-proof/export_children.txt'
if cf.exists():
    for l in cf.read_text().split('\n'):
        if l.strip(): t, c, cm = l.split(); kids.setdefault(t, []).append((c, cm))
# a child that the chain still declares as `HDec.c` (a kept copy) is not aliased (the alias would be ambiguous)
hdecl = set(l.split()[0] for l in (repo / 'scratch/one-proof/hashes_before.txt').read_text().split('\n') if l.strip())
# An alias `HDec.q1...qk.r` would shadow, inside `namespace HDec.q1...qj`, a declared `HDec.q1...qi.q(j+1)...qk.r`
# (i < j) that `q(j+1)...qk.r` resolved to before: such names are not aliased; their alias opens stay, reduced to them.
def shadows(n):
    p = n.split('.'); k = len(p) - 1
    return any('.'.join(['HDec'] + p[:i] + p[j:]) in hdecl for j in range(1, k + 1) for i in range(j))
pending = []  # (child, module) whose target is aliased but whose module is not reached yet
# `open ZInQ` before HDec.ZInQ is a namespace (LPrefix) opened the root ZInQ; keep that once the alias block
# registers HDec.ZInQ at the top of the module
FIX = {'LPrefix': [('open Real ZInQ', 'open Real _root_.ZInQ -- op-compact: root ZInQ, as before HDec.ZInQ was a namespace'),
                   ('open Real ZInQ Height', 'open Real _root_.ZInQ Height -- op-compact: root ZInQ, as before HDec.ZInQ was a namespace')]}
seen = set(); tot = [0, 0, 0, 0]
for mod in ORDER:
    p = repo / 'ZInQKernel/OneProof/H' / (mod + '.lean')
    lines = p.read_text(encoding='utf-8').split('\n')
    new = []; names = []; nrm = 0; hoist = {}
    R = reach('ZInQKernel.OneProof.H.' + mod)
    def addkid(c, cm):
        if c in seen or 'HDec.' + c in hdecl or shadows(c): return
        if cm in R: seen.add(c); names.append(c)
        else: pending.append((c, cm))
    for c, cm in pending[:]:
        pending.remove((c, cm)); addkid(c, cm)
    for i, l in enumerate(lines):
        m = TAGRE.match(l)
        # keep the lines that replace an original explicit-list open (op-dedupe `was:` comment just above)
        if m and any(x.startswith('-- op-dedupe was:') for x in lines[max(0, i - 2):i]): m = None
        if m:
            nrm += 1
            keep = [r for r in m.group(2).split() if shadows(m.group(1) + '.' + r)]
            for r in keep:
                if r not in hoist.setdefault(m.group(1), []): hoist[m.group(1)].append(r)
            for r in m.group(2).split():
                full = m.group(1) + '.' + r
                if r in keep: continue
                if full not in seen:
                    seen.add(full); names.append(full)
                    for c, cm in kids.get(full, []): addkid(c, cm)
            continue
        for a, b in FIX.get(mod, []):
            if l == a: l = b
        new.append(l)
    if names:
        groups = {}
        for n in names:
            t, rest = n.split('.', 1); groups.setdefault(t, []).append(rest)
        block = ['', '-- op-compact: aliases `HDec.T.x := T.x` for the copies deleted by op-dedupe (first used here)']
        for t, rs in groups.items():
            block.append(f'namespace HDec.{t} export _root_.{t} ({" ".join(rs)}) end HDec.{t}')
        # insert after the last leading import line
        k = 0
        while k < len(new) and (new[k].startswith('import ') or new[k].strip() == ''): k += 1
        j = max(i for i in range(k) if new[i].startswith('import ')) + 1
        new[j:j] = block
    if hoist:  # the shadowing names' alias opens, merged per namespace, once after `namespace HDec`
        j = new.index('namespace HDec') + 1
        new[j:j] = ['', '-- op-compact: these names are not aliased by `export` (an alias would shadow a declared `HDec` name)'] + \
            [f'open _root_.{q} ({" ".join(rs)}) -- op-dedupe' for q, rs in hoist.items()]
    out = '\n'.join(new)
    b0, b1 = len('\n'.join(lines).encode()), len(out.encode())
    print(f'{mod}\t{len(lines)}\t{b0}\t{len(new)}\t{b1}\t-{nrm} open lines\t+{len(names)} aliases')
    tot = [tot[0] + len(lines), tot[1] + b0, tot[2] + len(new), tot[3] + b1]
    if not dry: p.write_text(out, encoding='utf-8')
print('TOTAL', *tot, sep='\t')
print('children never reached:', len(pending), pending[:10])
