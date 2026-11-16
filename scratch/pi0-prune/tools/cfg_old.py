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
  ('TailD.lean', [S(35, 82, note='structure, docstring omitted'), S(85, 87), S(117, 119), S(128, 141), S(150, 154),
                  S(156, 181), S(192, 196), S(201, 253), S(255, 258), S(534, 537)]),
  ('TailE.lean', [S(6459, 6490, note='structure, docstring omitted'), S(6569, 6590)]),
  ('TailK.lean', [S(282, 342), S(344, 355)]),
  ('TailN.lean', [S(66, 97, note='structure, docstring omitted'), S(99, 123)]),
  ('TailO.lean', [S(2869, 2873), S(2875, 2880), S(2882, 2904), S(2906, 2911), S(2913, 2923)]),
  ('TailX.lean', [S(71, 108, note='structure, docstring omitted'), S(189, 215), S(244, 268), S(274, 280)]),
  ('TailZ4.lean', [S(66, 102, note='structure, docstring omitted'), S(151, 170), S(172, 178), S(180, 207), S(231, 251),
                   S(253, 260)]),
  ('TailZ9.lean', [S(25, 66, note='structure, docstring omitted'), S(88, 118), S(139, 145)]),
  ('TailZ11.lean', [S(51, 57)]),
  ('TailZ13.lean', [S(64, 70)]),
]
FOOTER = ''
