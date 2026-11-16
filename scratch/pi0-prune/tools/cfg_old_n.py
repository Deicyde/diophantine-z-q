exec(open('/home/jackmccarthy/dzq-wt/pi0-prune/scratch/pi0-prune/tools/common.py').read())
OUT = '/home/jackmccarthy/dzq-wt/pi0-prune/ZInQKernel/Contrib/OneProof/Pi0Prune/Old.lean'
HEADER = r'''import ZInQKernel.Contrib.OneProof.Pi0Prune.Base

/-!
# pi0-prune (2/3): the old bundle generations with the weak row

The six bundle structures that carry the row (`ResearchLeaves3` (TailD), `OpenResearchLeaves2` (TailE), `5` (TailN),
`7` (TailX), `8` (TailZ4), `9` (TailZ9)) copied verbatim with `r1r2 : LeafAdopt.R1R2fpRepW` (and `r1b : ∀ h :
LeafAdopt.R1R2fpRepW, …` with `R1R2fp_of_repW`), suffix `W`; and every declaration of the single proof whose type
mentions them, copied verbatim with the same renaming (each copy names its source file and lines at base 43513d87).
No `sorry`; standard axioms only.
-/

set_option linter.all false
set_option autoImplicit false
set_option maxHeartbeats 1000000
'''
def S(a, b, **kw):
    return (a, b, kw) if kw else (a, b)
SEGMENTS = [
  ('TailD.lean', [('ResearchLeaves3', {'note': 'structure, docstring omitted', 'nodoc': True}), ('ResearchLeaves3.h5', {}), ('reverseIsogeny_of_leaves3', {}), ('g8_g12_of_leaves3', {}), ('newformLeaves_of3', {}), ('afterG7_of3', {}), ('hom_of_common3', {}), ('glueOutputs_of_leaves3', {}), ('sixContactMin_of_leavesR3', {}), ('r1r2fpFull_of', {})]),
  ('TailE.lean', [('OpenResearchLeaves2', {'note': 'structure, docstring omitted', 'nodoc': True}), ('researchLeaves3_of_open2', {})]),
  ('TailK.lean', [('gluePieces_of_open4', {}), ('sixContactMin_of_open4', {})]),
  ('TailN.lean', [('OpenResearchLeaves5', {'note': 'structure, docstring omitted', 'nodoc': True}), ('researchLeaves2_of_open5', {})]),
  ('TailO.lean', [('cmDescends_of6', {}), ('qmHauptmodul_of6', {}), ('addedLeaves4_of_open6', {}), ('glue4_of_open6', {}), ('sixContactMin_of_open6', {})]),
  ('TailX.lean', [('OpenResearchLeaves7', {'note': 'structure, docstring omitted', 'nodoc': True}), ('researchLeaves5_of_open7', {}), ('addedLeaves6_of_open7', {}), ('sixContactMin_of_open7', {})]),
  ('TailZ4.lean', [('OpenResearchLeaves8', {'note': 'structure, docstring omitted', 'nodoc': True}), ('heightRowsNo20_of8', {}), ('r20Lower_of8', {}), ('researchLeaves7_of_open8', {}), ('addedLeaves7_of_open8', {}), ('sixContactMin_of_open8', {})]),
  ('TailZ9.lean', [('OpenResearchLeaves9', {'note': 'structure, docstring omitted', 'nodoc': True}), ('researchLeaves8_of_open9', {}), ('sixContactMin_of_open9', {})]),
  ('TailZ11.lean', [('sixContactMin_of_open10', {})]),
  ('TailZ13.lean', [('sixContactMin_of_open11', {})]),
]

FOOTER = ''
