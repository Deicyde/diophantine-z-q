#!/usr/bin/env python3
"""Compare each vendored Tau Ceti file with the tcport.py output from its source commit.
usage: diffcheck.py WORKTREE  -> prints files that differ (and missing provenance)."""
import os, re, sys, glob, difflib
wt = sys.argv[1]
srcs = {'5a01f5fe3621': os.path.expanduser('~/tc-oct16'), '97a5b235': os.path.expanduser('~/tc-nov01')}
pat = re.compile(r'^(\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?)TauCeti\.', re.M)
prov = re.compile(r'^-- Vendored from Tau Ceti \(https://github.com/TauCetiProject/TauCeti, commit ([0-9a-f]+), module ([\w.]+)\), Apache-2.0\.\n', re.M)
root = os.path.join(wt, 'ZInQKernel/Contrib/TauCeti')
n = same = 0
for f in sorted(glob.glob(root + '/**/*.lean', recursive=True)):
    rel = os.path.relpath(f, root); n += 1
    txt = open(f, encoding='utf-8').read()
    m = prov.search(txt)
    if not m:
        print('NOPROV', rel); continue
    sha, mod = m.groups()
    src = next((v for k, v in srcs.items() if k.startswith(sha) or sha.startswith(k)), None)
    s = os.path.join(src, *mod.split('.')) + '.lean'
    exp = pat.sub(r'\1ZInQKernel.Contrib.TauCeti.', open(s, encoding='utf-8').read())
    i = exp.find('-/\n')
    exp = exp[:i + 3] + m.group(0) + exp[i + 3:] if i >= 0 else m.group(0) + exp
    if exp == txt: same += 1; continue
    print('DIFF', rel, sha)
    if '-v' in sys.argv:
        sys.stdout.writelines(difflib.unified_diff(exp.splitlines(True), txt.splitlines(True), 'tc', 'ours', n=0))
print(f'{n} files, {same} identical to tcport output')
