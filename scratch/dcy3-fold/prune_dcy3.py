"""dcy3-fold step 2: after the threading (thread.py), delete `deligneComponentsY3Printed` from OpenAddedLeaves9 (TailZ13)
and `deligneComponentsY3PrintedAb` from OpenAddedLeaves10-17 (every generation of the lineage: the off-chain
generations 10 and 11 must go too, because addedLeaves11_of_open12 and addedLeaves10_of_open11 fill them from the next
generation), with every assignment into them. Deletions only. Prints every deleted line."""
import sys
sys.path.insert(0, 'scratch/dcy3-fold')
import prune_lib as P
P.drop_field('TailZ13', 'OpenAddedLeaves9', 'deligneComponentsY3Printed')
A = 'deligneComponentsY3PrintedAb'
for f, s in [('TailZ17', 'OpenAddedLeaves10'), ('TailZ18', 'OpenAddedLeaves11'), ('TailZ22', 'OpenAddedLeaves12'),
             ('TailZ24', 'OpenAddedLeaves13'), ('TailZ26', 'OpenAddedLeaves14'), ('TailZ30', 'OpenAddedLeaves15'),
             ('TailZ31', 'OpenAddedLeaves16'), ('TailZ34', 'OpenAddedLeaves17')]:
    P.drop_field(f, s, A)
P.drop_assign('TailZ17', 'theorem addedLeaves9_of_open10 ', 'deligneComponentsY3Printed',
    '  deligneComponentsY3Printed :=\n'
    '    (_root_.LeafQM.AV.R1UnivRigid.deligneComponentsY3Printed_iff_ab (mumfordRigidity_of11 r)).mpr\n'
    '      l.deligneComponentsY3PrintedAb')
P.drop_assign('TailZ23', 'theorem addedLeaves9_of_open14 ', 'deligneComponentsY3Printed',
    '  deligneComponentsY3Printed :=\n'
    '    (_root_.LeafQM.AV.R1UnivRigid.deligneComponentsY3Printed_iff_ab_gl\n'
    '      (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw)).mpr\n'
    '      l.deligneComponentsY3PrintedAb')
for f, h, v in [('TailZ18', 'theorem addedLeaves10_of_open11 ', 'l'), ('TailZ22', 'theorem addedLeaves11_of_open12 ', 'l'),
                ('TailZ24', 'theorem addedLeaves12_of_open13 ', 'l'),
                ('TailZ26', 'theorem openAddedLeaves13_of_OpenAddedLeaves14 ', 'n'),
                ('TailZ30', 'theorem openAddedLeaves14_of_OpenAddedLeaves15 ', 'n'),
                ('TailZ31', 'theorem openAddedLeaves15_of_OpenAddedLeaves16 ', 'n'),
                ('TailZ34', 'theorem openAddedLeaves16_of_OpenAddedLeaves17 ', 'n')]:
    P.drop_assign(f, h, A, f'  {A} := {v}.{A}')
if '--dry' not in sys.argv:
    for f, ls in P.files.items():
        open(P.H + f + '.lean', 'w').write('\n'.join(l for l in ls if l is not None))
for d in sorted(P.deleted):
    print(f'{d[0]}:{d[1]}  [{d[2]}]  {d[3]}')
