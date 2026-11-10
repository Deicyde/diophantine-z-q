#!/usr/bin/env python3
"""List the hunks of a unified diff of Version 13 against Version 14.

Usage: python3 -I hunks.py V13.tex V14.tex
Both files are read with carriage returns removed (the sources mix CRLF and LF).
For each hunk of `difflib.unified_diff` (3 lines of context, the same hunks as
`diff -u` / `git diff --no-index`), print its V13 and V14 line ranges, the numbers
of removed and added lines, the enclosing \\section / \\subsection in each file and
the \\label{...}s that occur in the changed lines.  Prints no manuscript text other
than section titles and labels.
"""
import re
import subprocess
import sys

SEC = re.compile(r'^\\(section|subsection|subsubsection)\*?\{(.*?)\}')
LAB = re.compile(r'\\label\{([^}]*)\}')


def read(path):
    with open(path, encoding='utf-8', errors='replace') as f:
        return f.read().replace('\r', '').split('\n')


def headings(lines):
    out = []
    for i, l in enumerate(lines, 1):
        m = SEC.match(l)
        if m:
            lab = LAB.search(l)
            out.append((i, m.group(1), m.group(2)[:60], lab.group(1) if lab else ''))
    return out


def where(heads, n):
    sec = sub = None
    for h in heads:
        if h[0] > n:
            break
        if h[1] == 'section':
            sec, sub = h, None
        elif h[1] == 'subsection':
            sub = h
    s = f'{sec[2]}' if sec else '-'
    if sub:
        s += f' / {sub[2]}'
    return s


def main():
    a, b = sys.argv[1], sys.argv[2]
    A, B = read(a), read(b)
    # use diff -u on CR-stripped copies piped through process substitution
    import tempfile, os
    with tempfile.TemporaryDirectory() as d:
        pa, pb = os.path.join(d, 'a'), os.path.join(d, 'b')
        open(pa, 'w').write('\n'.join(A))
        open(pb, 'w').write('\n'.join(B))
        r = subprocess.run(['diff', '-u', pa, pb], capture_output=True, text=True)
    ha, hb = headings(A), headings(B)
    hunk = re.compile(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@')
    hunks = []
    cur = None
    for l in r.stdout.split('\n'):
        m = hunk.match(l)
        if m:
            s1, n1, s2, n2 = int(m[1]), int(m[2] or 1), int(m[3]), int(m[4] or 1)
            cur = dict(a=(s1, s1 + n1 - 1), b=(s2, s2 + n2 - 1), rem=0, add=0,
                       labs_a=[], labs_b=[], first_a=None, first_b=None)
            hunks.append(cur)
            ia, ib = s1, s2
            continue
        if cur is None or not l:
            if cur is not None and l == '':
                ia += 1; ib += 1
            continue
        c = l[0]
        if c == ' ':
            ia += 1; ib += 1
        elif c == '-':
            cur['rem'] += 1
            cur['first_a'] = cur['first_a'] or ia
            cur['labs_a'] += LAB.findall(l)
            ia += 1
        elif c == '+':
            cur['add'] += 1
            cur['first_b'] = cur['first_b'] or ib
            cur['labs_b'] += LAB.findall(l)
            ib += 1
    tot_a = tot_r = 0
    for k, h in enumerate(hunks, 1):
        tot_a += h['add']; tot_r += h['rem']
        pa_ = h['first_a'] or h['a'][0]
        pb_ = h['first_b'] or h['b'][0]
        print(f"H{k:02d} V13 {h['a'][0]}-{h['a'][1]} V14 {h['b'][0]}-{h['b'][1]} "
              f"-{h['rem']} +{h['add']}")
        print(f"     V13 in: {where(ha, pa_)}")
        print(f"     V14 in: {where(hb, pb_)}")
        if h['labs_a']:
            print(f"     labels removed: {', '.join(h['labs_a'])}")
        if h['labs_b']:
            print(f"     labels added: {', '.join(h['labs_b'])}")
    print(f'{len(hunks)} hunks, +{tot_a} -{tot_r}')


if __name__ == '__main__':
    main()
