#!/usr/bin/env python3
"""Compare each vendored Tau Ceti file (ZInQKernel/Contrib/TauCeti at a given commit of this repo)
with the upstream file at the pin named in its 'Vendored from Tau Ceti' header line.
Normalization: drop the leading comment block (copyright /- ... -/ and the '-- Vendored' line),
and map 'ZInQKernel.Contrib.TauCeti.' -> 'TauCeti.' in the remaining text.
Usage: tc_compare.py REPO_COMMIT TC_REPO"""
import re, subprocess, sys
from collections import Counter

commit, tc = sys.argv[1], sys.argv[2]
def git(args, cwd='.'):
    return subprocess.run(['git'] + args, cwd=cwd, capture_output=True, text=True)

files = git(['ls-tree', '-r', '--name-only', commit, 'ZInQKernel/Contrib/TauCeti']).stdout.split()
pin_re = re.compile(r'Vendored from Tau Ceti \(https://github.com/TauCetiProject/TauCeti, commit ([0-9a-f]+), module ([A-Za-z0-9_.]+)\)')

def strip_header(s):
    lines = s.split('\n')
    i = 0
    # skip blank lines, a leading /- ... -/ block, and '--' comment lines
    while i < len(lines):
        l = lines[i].strip()
        if l == '' or l.startswith('--'):
            i += 1; continue
        if l.startswith('/-') and not l.startswith('/-!') and not l.startswith('/--'):
            while i < len(lines) and '-/' not in lines[i]:
                i += 1
            i += 1; continue
        break
    return '\n'.join(lines[i:]).rstrip('\n')

stats = Counter(); diffs = []
for f in files:
    if not f.endswith('.lean'):
        stats['non-lean'] += 1; continue
    src = git(['show', f'{commit}:{f}']).stdout
    m = pin_re.search(src)
    if not m:
        stats['no-pin-header'] += 1; diffs.append((f, 'NO PIN HEADER')); continue
    pin, mod = m.group(1), m.group(2)
    up_path = mod.replace('.', '/') + '.lean'
    r = git(['show', f'{pin}:{up_path}'], cwd=tc)
    if r.returncode != 0:
        stats['upstream-missing'] += 1; diffs.append((f, f'upstream {pin}:{up_path} missing')); continue
    a = strip_header(src).replace('ZInQKernel.Contrib.TauCeti.', 'TauCeti.')
    b = strip_header(r.stdout)
    if a == b:
        stats[f'identical@{pin[:8]}'] += 1
    else:
        stats['DIFFERENT'] += 1; diffs.append((f, f'code differs from {pin[:8]}:{up_path}'))
print(dict(stats))
for f, why in diffs:
    print('DIFF', f, '--', why)
