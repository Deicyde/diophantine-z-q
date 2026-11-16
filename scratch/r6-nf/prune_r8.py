"""r6-nf step 1: prune the dead r8 (PkgI2.GrothendieckMonodromy) from the chain's old research bundles
(ResearchLeaves3, OpenResearchLeaves2/5/7/8) and the three OpenResearchLeaves9 fields that fed only r8
(semistableReductionDVR, semistableUnipotent, neronSchemeModelExistsDVR; PruneScan base: unused), with the
assignments into them. Deletions only. Run from the repository root; prints every deleted line."""
import sys
sys.path.insert(0, 'scratch/r6-nf')
import prune_lib as P
for f, s, fl in [('TailD', 'ResearchLeaves3', 'r8'), ('TailE', 'OpenResearchLeaves2', 'r8'),
                 ('TailN', 'OpenResearchLeaves5', 'r8'), ('TailX', 'OpenResearchLeaves7', 'r8'),
                 ('TailZ4', 'OpenResearchLeaves8', 'r8'),
                 ('TailZ9', 'OpenResearchLeaves9', 'semistableReductionDVR'),
                 ('TailZ9', 'OpenResearchLeaves9', 'semistableUnipotent'),
                 ('TailZ9', 'OpenResearchLeaves9', 'neronSchemeModelExistsDVR')]:
    P.drop_field(f, s, fl)
for f, h, fl, ex in [
        ('TailD', 'theorem researchLeaves3_of ', 'r8', '    r8 := r.r8,'),
        ('TailE', 'theorem researchLeaves3_of_open2 ', 'r8', '  r8 := r.r8'),
        ('TailN', 'theorem researchLeaves2_of_open5 ', 'r8', '  r8 := grothendieckMonodromy_ofK5 r.r8'),
        ('TailX', 'theorem researchLeaves5_of_open7 ', 'r8', '  r8 := r.r8'),
        ('TailZ4', 'theorem researchLeaves7_of_open8 ', 'r8', '  r8 := r.r8'),
        ('TailZ9', 'theorem researchLeaves8_of_open9 ', 'r8',
         '  r8 := _root_.ReductSplit.grothendieckMonodromy_final\' r.semistableReductionDVR r.semistableUnipotent\n'
         '    r.neronSchemeModelExistsDVR t.mumfordTorsionAlgClosed'),
        ('TailZ15', 'theorem researchLeaves9_of_open10 ', 'semistableReductionDVR', '  semistableReductionDVR := r.semistableReductionDVR'),
        ('TailZ15', 'theorem researchLeaves9_of_open10 ', 'semistableUnipotent', '  semistableUnipotent := r.semistableUnipotent'),
        ('TailZ15', 'theorem researchLeaves9_of_open10 ', 'neronSchemeModelExistsDVR', '  neronSchemeModelExistsDVR := r.neronSchemeModelExistsDVR'),
        ('TailZ23', 'theorem researchLeaves9_of_open14 ', 'semistableReductionDVR', '  semistableReductionDVR := semistableReductionDVR_of14 r t'),
        ('TailZ23', 'theorem researchLeaves9_of_open14 ', 'semistableUnipotent', '  semistableUnipotent := r.semistableUnipotent'),
        ('TailZ23', 'theorem researchLeaves9_of_open14 ', 'neronSchemeModelExistsDVR', '  neronSchemeModelExistsDVR := r.neronSchemeModelExistsDVR')]:
    P.drop_assign(f, h, fl, ex)
for f, ls in P.files.items():
    open(P.H + f + '.lean', 'w').write('\n'.join(l for l in ls if l is not None))
for d in sorted(P.deleted):
    print(f'{d[0]}:{d[1]}  [{d[2]}]  {d[3]}')
