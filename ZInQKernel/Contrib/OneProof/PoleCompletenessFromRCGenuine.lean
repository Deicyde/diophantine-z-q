import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRC
import ZInQKernel.Contrib.OneProof.PoleS12.Realization
import ZInQKernel.Contrib.OneProof.PoleS12.Leaves
import ZInQKernel.Contrib.OneProof.PoleS12.CountS12
import ZInQKernel.Contrib.OneProof.PoleS12.GoodUnram

/-!
# Theorem 5.2 from the printed Theorem 5.3 (fork issue #83, round 2)

Task pc-s12. Report: `docs/research/pc-s12.md`.

`poleCompleteness_of_restrictedConverseGenuine` proves `Manuscript.PoleCompleteness` (Theorem 5.2)
from `SelmerTwoPower.RestrictedConverseGenuine` (Theorem 5.3 as printed: the Selmer condition is
`corank_{ℤ₂} Sel_{2^∞}(E_ℓ/ℚ) = 1` over Tau Ceti's Galois cohomology), with

* `MatrixRealization` proved (`PoleS12.matrixRealization`, from S12's
  `par:simultaneous-matrices`, ELLIOT (supplement));
* Lemma 5.4 as a printed leaf over the genuine `Sel₂` and `Sel_{2^∞}` (`PoleS12.Lemma54`) and the
  Kummer identification `#Sel₂(E_ℓ/ℚ) = #SelM ℓ` (`PoleS12.KummerSelmerM`, textbook GLUE);
* Lemma 5.5 from the printed leaf `PoleS12.BCDTThmA`, the cited statement `PoleS12.KolyvaginThm1`
  (GLUE; with finite `Ш`), and Mordell's theorem;
* the local images of the Kummer map of `E_ℓ` (round 1's GLUE Props; see `PoleS12.LocalS12` for
  their status).

The abstract-`P` development (`poleCompleteness_of_restrictedConverse_final`) is kept; this file
instantiates `P := SelmerTwoPower.SelmerCorankOne`.
-/

namespace ZInQ.Manuscript.PoleS12

open ZInQ.Manuscript.PoleRC ZInQ.Manuscript.SelmerTwoPower

/-- **Theorem 5.2 from the printed Theorem 5.3, with round 1's local-image Props** (kept for
comparison; superseded by `poleCompleteness_of_restrictedConverseGenuine`). -/
theorem poleCompleteness_of_restrictedConverseGenuine_local (hRC : RestrictedConverseGenuine)
    (h54 : Lemma54) (hKum : KummerSelmerM) (hB : BCDTThmA) (hK : KolyvaginThm1)
    (hMW : MordellWeil) (hTwo : LocalTwo) (hThree : LocalThree) (hBad : LocalBad)
    (hGood : LocalGood) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse_final SelmerCorankOne hRC
    (lemma54At_of_printed h54 hKum) (kolyvaginRankOne_of_printed hB hK) hMW matrixRealization
    hTwo hThree hBad hGood

/-- **The dimension-three count** (tex L1061–1074), proved: S12's `par:descent` with every local
condition in Lean. -/
theorem dimThreeCount : DimThreeCount := dimThreeCount_S12 localGoodUnram

/-- **The simultaneous construction** (tex L1033–1074), proved (S12's `par:simultaneous-matrices`
and `par:descent`). -/
theorem simultaneousConstruction : SimultaneousConstruction :=
  simultaneousConstruction_of matrixRealization dimThreeCount

/-- **Theorem 5.2 from the printed Theorem 5.3** (`diophantine_zq.tex` L1019–1121): the final
form. Proved in Lean: the bookkeeping, the rescaling, the complete 2-descent, `MatrixRealization`
(S12 `par:simultaneous-matrices`), every local condition of the dimension-three count
(S12 `par:descent`). Remaining: Theorem 5.3 (`RestrictedConverseGenuine`), the printed leaves
`Lemma54`, `BCDTThmA`, `KolyvaginThm1`, `MordellWeil`, and the GLUE statement `KummerSelmerM`
(the Kummer identification `#Sel₂(E_ℓ/ℚ) = #SelM ℓ`, Silverman X.1.4).
ON THE SPOT (correction (c)): of `KolyvaginThm1` only the rank is used; finiteness of Ш
(tex L1107–1109) is replaced by the counting argument of `descentGlueM`. -/
theorem poleCompleteness_of_restrictedConverseGenuine (hRC : RestrictedConverseGenuine)
    (h54 : Lemma54) (hKum : KummerSelmerM) (hB : BCDTThmA) (hK : KolyvaginThm1)
    (hMW : MordellWeil) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_crm
    (crm_of_restrictedConverse SelmerCorankOne hRC (lemma54At_of_printed h54 hKum)
      (kolyvaginRankOne_of_printed hB hK) hMW descentGlueM)
    simultaneousConstruction

/-- **Theorem 5.2 from Theorem 5.3 over the abstract predicate** (round 1's form, with every GLUE
statement except `Lemma54At P` now proved). -/
theorem poleCompleteness_of_restrictedConverse_abstract (P : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse P) (h54 : Lemma54At P) (hK : KolyvaginRankOne)
    (hMW : MordellWeil) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_crm (crm_of_restrictedConverse P hRC h54 hK hMW descentGlueM)
    simultaneousConstruction

end ZInQ.Manuscript.PoleS12
