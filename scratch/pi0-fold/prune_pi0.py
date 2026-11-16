"""pi0-fold step 2: after the threading (thread.py: the chain carries the weak row R1R2fpRepW and x6Rows_of_open14 no
longer reads the two fields), delete `deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure` from every generation
that has them (OpenAddedLeaves12 (TailZ22), 13 (TailZ24), 14 (TailZ26), 15 (TailZ30), 16 (TailZ31), 17 (TailZ34)),
every assignment into them, and the dead readers of the generation-12 fields: x6-fold's off-chain
`x6Rows_of_open13`, `researchLeaves12_of_open13`, `addedLeaves11_of_open12`, `sixContactMin_of_open16` (TailZ22;
leaf-fold14's maps go from generation 14 to 9 directly). Deletions only. Prints every deleted line."""
import sys
sys.path.insert(0, 'scratch/pi0-fold')
import prune_lib as P
FS = ['deligneComponentsX6PrintedAb', 'geomConnOfAlgClosure']
for f, s in [('TailZ22', 'OpenAddedLeaves12'), ('TailZ24', 'OpenAddedLeaves13'), ('TailZ26', 'OpenAddedLeaves14'),
             ('TailZ30', 'OpenAddedLeaves15'), ('TailZ31', 'OpenAddedLeaves16'), ('TailZ34', 'OpenAddedLeaves17')]:
    for A in FS:
        P.drop_field(f, s, A)
for f, h, v in [('TailZ24', 'theorem addedLeaves12_of_open13 ', 'l'),
                ('TailZ26', 'theorem openAddedLeaves13_of_OpenAddedLeaves14 ', 'n'),
                ('TailZ30', 'theorem openAddedLeaves14_of_OpenAddedLeaves15 ', 'n'),
                ('TailZ31', 'theorem openAddedLeaves15_of_OpenAddedLeaves16 ', 'n'),
                ('TailZ34', 'theorem openAddedLeaves16_of_OpenAddedLeaves17 ', 'n')]:
    for A in FS:
        P.drop_assign(f, h, A, f'  {A} := {v}.{A}')
for n in ['sixContactMin_of_open16', 'addedLeaves11_of_open12', 'researchLeaves12_of_open13', 'x6Rows_of_open13']:
    P.drop_decl('TailZ22', n)
if '--dry' not in sys.argv:
    for f, ls in P.files.items():
        open(P.H + f + '.lean', 'w').write('\n'.join(l for l in ls if l is not None))
for d in sorted(P.deleted):
    print(f'{d[0]}:{d[1]}  [{d[2]}]  {d[3]}')
