"""assemble-port: LeavesP.lean = Leaves.lean (= scratch/h-decomposition/Leaves.lean) with leaf-fold2's prefix edit
(scratch/leaf-fold2/mk_prefix.py, edit 2, verbatim logic): the ten `TextbookLeaves` fields no proof uses (t1, t2, t3, t4,
t16b, t20, t21, t28, t29a, t29b) are deleted from `structure TextbookLeaves` and from `textbookLeaves_of_open`.
(leaf-fold2's edit 1, the extra imports, is done by assemble.sh from imports_extra.txt.) Run from scratch/assemble-port."""
import re
s = open('Leaves.lean').read()
drop = ['t1','t2','t3','t4','t16b','t20','t21','t28','t29a','t29b']
a = s.index('structure TextbookLeaves : Prop where'); b = s.index('\n\n\n', a)
new = []
for l in s[a:b].split('\n'):
    m = re.match(r'  (t\w+) :', l)
    if m and m.group(1) in drop:
        new.append('  -- leaf-fold2: field `%s` deleted (no proof on the route uses it; g0-assemble2 §7)' % m.group(1)); continue
    new.append(l)
nb = '\n'.join(new); assert nb.count('deleted') == 10
s = s[:a] + nb + s[b:]
a = s.index('theorem textbookLeaves_of_open (t : OpenTextbookLeaves) : TextbookLeaves where'); b = s.index('\n\n', a)
lines = s[a:b].split('\n'); new = [l for l in lines if not (re.match(r'  (t\w+) :=', l) and re.match(r'  (t\w+) :=', l).group(1) in drop)]
assert len(lines) - len(new) == 10
s = s[:a] + '\n'.join(new) + s[b:]
open('LeavesP.lean', 'w').write(s); print('ok', s.count('\n'))
