"""List the OneProof/H declarations with a `PkgI3.QMDichotomyYu` binder and every reference to them."""
import re, glob, os
H = 'ZInQKernel/OneProof/H/'
files = sorted(glob.glob(H + '*.lean'))
decl_re = re.compile(r'^(?:private )?(?:theorem|def|lemma) ([^\s(:]+)')
names = {}
for f in files:
    lines = open(f).read().split('\n')
    cur = None
    for i, l in enumerate(lines):
        m = decl_re.match(l)
        if m: cur = (m.group(1), i + 1)
        if cur and re.search(r'\(\w+ : PkgI3\.QMDichotomyYu\)', l) and not l.startswith('  t27 :'):
            names[cur[0]] = (os.path.basename(f), cur[1])
for n, (f, i) in sorted(names.items(), key=lambda x: x[1]):
    print(f'DECL {f}:{i} {n}')
for f in files:
    for i, l in enumerate(open(f).read().split('\n')):
        if l.startswith('#print'): continue
        for n in names:
            base = n.split('.')[-1]
            if re.search(r'(?<![\w\'.])' + re.escape(base) + r'(?![\w\'])', l) and not decl_re.match(l):
                print(f'  USE {os.path.basename(f)}:{i+1} [{n}] {l.strip()[:150]}')
