import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRC
import ZInQKernel.Contrib.PoleRC.Simultaneous

/-!
# Theorem 5.2 from Theorem 5.3, with the matrix realization proved

`MatrixRealization` (`diophantine_zq.tex` lines 1033–1060) is proved in
`ZInQKernel/Contrib/PoleRC/Simultaneous.lean` (`Simul.matrixRealization`), following the
simultaneous matrix/prime construction of the retained source S12 (Lemma
`par:simultaneous-matrices`). It therefore leaves the hypotheses of the final assembly.
-/

namespace ZInQ.Manuscript.PoleRC

/-- **The simultaneous construction from the four local images** (lines 1033–1074): the matrix
realization is proved, and the dimension-three count follows from the local images
(`dimThreeCount_of_local`). -/
theorem simultaneousConstruction_of_local (hTwo : LocalTwo) (hThree : LocalThree)
    (hBad : LocalBad) (hGood : LocalGood) : SimultaneousConstruction :=
  Simul.simultaneousConstruction_of_dimThree (dimThreeCount_of_local hTwo hThree hBad hGood)

/-- **Theorem 5.2 from Theorem 5.3, with `MatrixRealization` proved.** What remains is
Theorem 5.3, Lemma 5.4 at `E_ℓ` (interface for the abstract Selmer predicate), the printed
leaves of Lemma 5.5 (`KolyvaginRankOne`), Mordell's theorem, and the four textbook local
images. -/
theorem poleCompleteness_of_restrictedConverse_matrix (SelmerCorankOne : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse SelmerCorankOne) (h54 : Lemma54At SelmerCorankOne)
    (hK : KolyvaginRankOne) (hMW : MordellWeil) (hTwo : LocalTwo) (hThree : LocalThree)
    (hBad : LocalBad) (hGood : LocalGood) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse_final SelmerCorankOne hRC h54 hK hMW
    Simul.matrixRealization hTwo hThree hBad hGood

end ZInQ.Manuscript.PoleRC
