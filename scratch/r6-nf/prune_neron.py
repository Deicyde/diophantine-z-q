"""r6-nf step 3b: after the reroute, PruneScan reports OpenResearchLeaves21.neronSchemeModelExistsDVR unused; delete the
field from generations 14-21 (TailZ23 ... TailZ34; the off-chain generations 10-13 keep theirs, as in earlier prunes),
the 7 assignments into them, and the dead reader ss1_ss3_of14 (DeadCascade). Deletions only. Prints every deleted line."""
import sys
sys.path.insert(0, 'scratch/r6-nf')
import prune_lib as P
FLD = 'neronSchemeModelExistsDVR'
for f, s in [('TailZ23', 'OpenResearchLeaves14'), ('TailZ25', 'OpenResearchLeaves15'), ('TailZ26', 'OpenResearchLeaves16'),
             ('TailZ27', 'OpenResearchLeaves17'), ('TailZ28', 'OpenResearchLeaves18'), ('TailZ29', 'OpenResearchLeaves19'),
             ('TailZ33', 'OpenResearchLeaves20'), ('TailZ34', 'OpenResearchLeaves21')]:
    P.drop_field(f, s, FLD)
for f, h in [('TailZ25', 'theorem openResearchLeaves14_of_OpenResearchLeaves15 '),
             ('TailZ26', 'theorem openResearchLeaves15_of_OpenResearchLeaves16 '),
             ('TailZ27', 'theorem openResearchLeaves16_of_OpenResearchLeaves17 '),
             ('TailZ28', 'theorem openResearchLeaves17_of_OpenResearchLeaves18 '),
             ('TailZ29', 'theorem openResearchLeaves18_of_OpenResearchLeaves19 '),
             ('TailZ33', 'theorem openResearchLeaves19_of_OpenResearchLeaves20 '),
             ('TailZ34', 'theorem openResearchLeaves20_of_OpenResearchLeaves21 ')]:
    P.drop_assign(f, h, FLD, f'  {FLD} := n.{FLD}')
for f, n in [('TailZ23', 'ss1_ss3_of14')]:   # dead-cascade.txt minus generated casesOn/recOn
    P.drop_decl(f, n)
for f, ls in P.files.items():
    open(P.H + f + '.lean', 'w').write('\n'.join(l for l in ls if l is not None))
for d in sorted(P.deleted):
    print(f'{d[0]}:{d[1]}  [{d[2]}]  {d[3]}')
