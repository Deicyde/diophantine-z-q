#!/usr/bin/env python3
"""olean/LPrefix.lean = scratch/h-decomposition/Leaves.lean with two edits (leaf-fold2):
 1. g0-assemble2's imports_extra.txt added after the imports (as g0-assemble2's assemble.sh does);
 2. the ten TextbookLeaves fields that no proof uses (g0-assemble2 §7: t1, t2, t3, t4, t16b, t20, t21,
    t28, t29a, t29b) are deleted from `structure TextbookLeaves` and from `textbookLeaves_of_open`.
    Lean then checks that nothing uses them."""
import re, sys
src = open('../h-decomposition/Leaves.lean').read().split('\n')
extra = open('../g0-assemble2/imports_extra.txt').read().strip().split('\n')
drop = ['t1','t2','t3','t4','t16b','t20','t21','t28','t29a','t29b']
out = []
# imports
nimp = max(i for i,l in enumerate(src[:20]) if l.startswith('import '))
out = src[:nimp+1] + extra + src[nimp+1:]
s = '\n'.join(out)
# structure TextbookLeaves
a = s.index('structure TextbookLeaves : Prop where')
b = s.index('\n\n\n', a)
block = s[a:b]
lines = block.split('\n'); new = []
for l in lines:
    m = re.match(r'  (t\w+) :', l)
    if m and m.group(1) in drop:
        new.append('  -- leaf-fold2: field `%s` deleted (no proof on the route uses it; g0-assemble2 §7)' % m.group(1)); continue
    new.append(l)
nb = '\n'.join(new)
assert nb.count('deleted') == 10, nb.count('deleted')
s = s[:a] + nb + s[b:]
a = s.index('theorem textbookLeaves_of_open (t : OpenTextbookLeaves) : TextbookLeaves where')
b = s.index('\n\n', a)
lines = s[a:b].split('\n'); new = []
for l in lines:
    m = re.match(r'  (t\w+) :=', l)
    if m and m.group(1) in drop: continue
    new.append(l)
assert len(lines) - len(new) == 10
s = s[:a] + '\n'.join(new) + s[b:]
# leaf-fold3: the three items of the fork's issue #2 that touch Leaves.lean
# (2) the kernel's strengthened fibre_conjugates_isomorphic (ZInQKernel/HDecomp/QM/Leaves.lean:500), with its proof
a = s.index('theorem fibre_conjugates_isomorphic (h : R1R2fp) (j₀ : ℚ) :')
da = s.rindex('/-- **Glue (compiled): A4 + A7 from the leaves alone.**', 0, a)
b = s.index('\n\n', a)
k = open('../../ZInQKernel/HDecomp/QM/Leaves.lean').read()
ka = k.index('theorem fibre_conjugates_isomorphic (h : R1R2fp) (j₀ : ℚ) :')
kda = k.rindex('/--', 0, ka)
kb = k.index('\n\n', ka)
s = s[:da] + k[kda:kb] + s[b:]
# (5) the duplicated `#print axioms HSyn.sixContactMin_of_leaves` (keep the first)
t = '\n#print axioms HSyn.sixContactMin_of_leaves\n'
i1 = s.index(t); i2 = s.index(t, i1 + 1)
s = s[:i2] + '\n' + s[i2 + len(t):]
assert s.count(t) == 1
# (8) the QM "Lemma P" (rv-qm-polar) becomes "Lemma QP" (route AP has its own Lemma P)
n8 = len(re.findall(r'Lemma P\b', s))
s = re.sub(r'Lemma P\b', 'Lemma QP', s)
s = s.replace('`lemmaP_lattice`', '`lemmaP_lattice` (Lemma QP; Lean name unchanged in rv-qm-polar and the kernel)')
print('issue#2: Lemma P renamed', n8)
open('olean/LPrefix.lean','w').write(s)
print('ok', s.count('\n'))
