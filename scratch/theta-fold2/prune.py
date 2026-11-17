"""theta-fold2 step 2: after step 1 (plumb.py: gluePieces_of_open4 reads the use form hθ, not the field), delete
`thetaRatiosAlgebraic` from every generation in PruneScan's prune set (prune-set-step1.txt: OpenAddedLeaves4 (TailK),
6 (TailO), 7 (TailX), 8 (TailZ4), 9 (TailZ13), 12 (TailZ22), 13 (TailZ24), 14 (TailZ26), 15 (TailZ30), 16 (TailZ31),
17 (TailZ34)), every assignment into them, and the element `l.thetaRatiosAlgebraic` of the anonymous constructor
of `OpenAddedLeaves4` in TailO's `openAddedLeaves4_of_Q5`. Older off-closure bundles (GluePieces2/3,
OpenAddedLeaves2/3/5/10/11, OpenAddedLeavesQ5-Q10) keep the field. Prints every deleted line."""
import sys
sys.path.insert(0, 'scratch/theta-fold2')
import prune_lib as P
A = 'thetaRatiosAlgebraic'
for f, s in [('TailK', 'OpenAddedLeaves4'), ('TailO', 'OpenAddedLeaves6'), ('TailX', 'OpenAddedLeaves7'),
             ('TailZ4', 'OpenAddedLeaves8'), ('TailZ13', 'OpenAddedLeaves9'), ('TailZ22', 'OpenAddedLeaves12'),
             ('TailZ24', 'OpenAddedLeaves13'), ('TailZ26', 'OpenAddedLeaves14'), ('TailZ30', 'OpenAddedLeaves15'),
             ('TailZ31', 'OpenAddedLeaves16'), ('TailZ34', 'OpenAddedLeaves17')]:
    P.drop_field(f, s, A)
for f, h, v in [('TailN', 'theorem addedLeaves4_of_open5 ', 'l'),
                ('TailO', 'theorem addedLeaves4_of_open6 ', 'l'),
                ('TailX', 'theorem addedLeaves6_of_open7 ', 'l'),
                ('TailZ4', 'theorem addedLeaves7_of_open8 ', 'l'),
                ('TailZ13', 'theorem addedLeaves8_of_open9 ', 'l'),
                ('TailZ17', 'theorem addedLeaves9_of_open10 ', 'l'),
                ('TailZ23', 'theorem addedLeaves9_of_open14 ', 'l'),
                ('TailZ24', 'theorem addedLeaves12_of_open13 ', 'l'),
                ('TailZ26', 'theorem openAddedLeaves13_of_OpenAddedLeaves14 ', 'n'),
                ('TailZ30', 'theorem openAddedLeaves14_of_OpenAddedLeaves15 ', 'n'),
                ('TailZ31', 'theorem openAddedLeaves15_of_OpenAddedLeaves16 ', 'n'),
                ('TailZ34', 'theorem openAddedLeaves16_of_OpenAddedLeaves17 ', 'n')]:
    P.drop_assign(f, h, A, f'  {A} := {v}.{A}')
# the anonymous constructor of OpenAddedLeaves4 from OpenAddedLeavesQ5 (TailO)
ls = P.get('TailO')
a = P.find('TailO', lambda l: l.startswith('theorem openAddedLeaves4_of_Q5 '))
assert len(a) == 1
i = a[0] + 1
old = '  ⟨l.cmOptimalEmbedding, l.thetaRatiosAlgebraic, l.qmHauptmodul, l.qmClassNumberOne, l.senTwist,'
assert ls[i] == old, ls[i]
P.deleted.append(('TailO', i + 1, 'element l.thetaRatiosAlgebraic in openAddedLeaves4_of_Q5 (line edited)', ls[i]))
ls[i] = '  ⟨l.cmOptimalEmbedding, l.qmHauptmodul, l.qmClassNumberOne, l.senTwist,'
if '--dry' not in sys.argv:
    for f, ls in P.files.items():
        open(P.H + f + '.lean', 'w').write('\n'.join(l for l in ls if l is not None))
for d in sorted(P.deleted):
    print(f'{d[0]}:{d[1]}  [{d[2]}]  {d[3]}')
