import ZInQKernel.Contrib.PoleRC.Reduction
import ZInQKernel.Contrib.PoleRC.CRM
import ZInQKernel.Contrib.PoleRC.Matrix
import ZInQKernel.Contrib.PoleRC.Count
import ZInQKernel.Contrib.PoleRC.DescentM

/-!
# Theorem 5.2 (`Manuscript.PoleCompleteness`) from Theorem 5.3 (`Manuscript.RestrictedConverse`)

Fork issue #83 (task pc-from-rc). Report: `docs/research/pc-from-rc.md`.

`poleCompleteness_of_restrictedConverse` proves the manuscript's Theorem 5.2 from

* Theorem 5.3 (`Manuscript.RestrictedConverse P`), for an abstract Selmer predicate `P`;
* `Lemma54At P` (Lemma 5.4 at `E_ℓ`, what is needed of `P`);
* `KolyvaginRankOne` (Lemma 5.5, rank half: BCDT Theorem A and Kolyvagin Theorem 1; printed
  leaves) and `MordellWeil` (textbook);
* GLUE statements, not proved in Lean: `DescentGlueM` (complete 2-descent of `E_ℓ`),
  `MatrixRealization` (lines 1033–1060, ELLIOT: S11–S12), and either `DimThreeCount`
  (lines 1061–1074) or, in `poleCompleteness_of_restrictedConverse_local`, the four local images
  `LocalTwo`, `LocalThree`, `LocalBad`, `LocalGood` from which `dimThreeCount_of_local` proves it.

Proved in Lean here: the squareclass bookkeeping (lines 1020–1032), the rescaling to the eleven
witnesses (lines 1107–1121), and the assembly.
-/

namespace ZInQ.Manuscript.PoleRC

/-- **Theorem 5.2 from `CR_M`, the realization and the dimension-three count.** -/
theorem poleCompleteness_of_crm_glue (hCR : CRM) (hR : MatrixRealization) (hD : DimThreeCount) :
    Manuscript.PoleCompleteness :=
  poleCompleteness_of_crm hCR (simultaneousConstruction_of hR hD)

/-- **Theorem 5.2 from Theorem 5.3** (`diophantine_zq.tex` lines 1019–1121), with Lemma 5.4 at
`E_ℓ` against the abstract Selmer predicate, the printed leaves of Lemma 5.5, Mordell's theorem,
and the three GLUE statements. -/
theorem poleCompleteness_of_restrictedConverse (SelmerCorankOne : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse SelmerCorankOne) (h54 : Lemma54At SelmerCorankOne)
    (hK : KolyvaginRankOne) (hMW : MordellWeil) (hDesc : DescentGlueM)
    (hR : MatrixRealization) (hD : DimThreeCount) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_crm_glue
    (crm_of_restrictedConverse SelmerCorankOne hRC h54 hK hMW hDesc) hR hD

/-- **Theorem 5.2 from Theorem 5.3, with the dimension-three count proved** from the local images
of the Kummer map of `E_ℓ` at `2`, `3`, the primes of `ℓ` and the primes of good reduction
(textbook GLUE; the real place is proved, `localReal`). -/
theorem poleCompleteness_of_restrictedConverse_local (SelmerCorankOne : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse SelmerCorankOne) (h54 : Lemma54At SelmerCorankOne)
    (hK : KolyvaginRankOne) (hMW : MordellWeil) (hDesc : DescentGlueM)
    (hR : MatrixRealization) (hTwo : LocalTwo) (hThree : LocalThree) (hBad : LocalBad)
    (hGood : LocalGood) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse SelmerCorankOne hRC h54 hK hMW hDesc hR
    (dimThreeCount_of_local hTwo hThree hBad hGood)

/-- **Theorem 5.2 from Theorem 5.3: the final form.** The complete 2-descent (`descentGlueM`) and
the dimension-three count (`dimThreeCount_of_local`) are proved; what remains is Theorem 5.3,
Lemma 5.4 at `E_ℓ` (interface for the abstract Selmer predicate), the printed leaves of Lemma 5.5
(`KolyvaginRankOne`) and Mordell's theorem, the realization of the matrix conditions
(`MatrixRealization`, ELLIOT: S11–S12), and the four textbook local images. -/
theorem poleCompleteness_of_restrictedConverse_final (SelmerCorankOne : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse SelmerCorankOne) (h54 : Lemma54At SelmerCorankOne)
    (hK : KolyvaginRankOne) (hMW : MordellWeil) (hR : MatrixRealization) (hTwo : LocalTwo)
    (hThree : LocalThree) (hBad : LocalBad) (hGood : LocalGood) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse_local SelmerCorankOne hRC h54 hK hMW descentGlueM hR
    hTwo hThree hBad hGood

end ZInQ.Manuscript.PoleRC
