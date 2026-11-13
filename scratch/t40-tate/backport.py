#!/usr/bin/env python3
"""Backport full Tau Ceti main modules under ZInQKernel/Contrib/TauCeti/Backport/.
usage: backport.py LIST   (modules TauCeti.A.B; source ~/tc-main)
Imports TauCeti.X -> Backport.X if X is in LIST, else ZInQKernel.Contrib.TauCeti.X (vendored)."""
import os, re, subprocess, sys
src = os.path.expanduser('~/tc-main')
sha = subprocess.run(['git','-C',src,'rev-parse','HEAD'],capture_output=True,text=True).stdout.strip()
mods = [l.strip() for l in open(sys.argv[1]) if l.strip()]
force = '--force' in sys.argv
S = set(mods) | set(l.strip() for l in open('scratch/t40-tate/extras-list.txt') if l.strip())
pat = re.compile(r'^(\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?)(TauCeti\.\S+)', re.M)
def rw(m):
    x = m.group(2)
    if x in S: return m.group(1) + 'ZInQKernel.Contrib.TauCeti.Backport.' + x[len('TauCeti.'):]
    return m.group(1) + 'ZInQKernel.Contrib.' + x
for m in mods:
    parts = m.split('.')
    d = os.path.join('ZInQKernel/Contrib/TauCeti/Backport', *parts[1:]) + '.lean'
    if os.path.exists(d) and not force: continue
    os.makedirs(os.path.dirname(d), exist_ok=True)
    txt = open(os.path.join(src, *parts) + '.lean', encoding='utf-8').read()
    txt = pat.sub(rw, txt)
    note = (f'-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit {sha[:12]}, module\n'
            f'-- {m}), Apache-2.0: the whole module (task t40-tate), placed under Backport/.\n'
            f'-- Modified for the Z-in-Q kernel: imports rewritten to the vendored and Backport/ modules.\n')
    i = txt.find('-/\n')
    txt = txt[:i+3] + note + txt[i+3:]
    open(d, 'w', encoding='utf-8').write(txt)
    print('wrote', d)
