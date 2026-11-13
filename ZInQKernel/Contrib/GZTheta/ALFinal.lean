import ZInQKernel.Contrib.GZTheta.ALMain
import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne.Across

/-!
# atkin-li: strong multiplicity one across levels, and Atkin–Li's twist theorem

Task atkin-li. `NewformUniqueAcrossLevels` is Tau Ceti main's
`HeckeRing.GL2.Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq` (commit 4d91513e, backported to
`ZInQKernel/Contrib/TauCeti/Backport/NumberTheory/ModularForms/Newforms/StrongMultiplicityOne/
Across.lean`) with the finite exceptional set empty. With it, gz-theta's `AtkinLiTwistNew`
(Atkin–Li, Invent. Math. 48 (1978), Thm 3.1, for weight 2, trivial nebentypus and quadratic
characters `(·/r)`, `r ≡ 1 mod 4`) is proved.
-/

open HeckeRing.GL2

namespace ZInQ.GZTheta

/-- **Strong multiplicity one across levels** (Miyake 4.6.19, 4.6.20). -/
theorem newformUniqueAcrossLevels : NewformUniqueAcrossLevels := by
  intro N _ k M M' _ _ χ g g' hM hM' hgχ hg'χ h
  exact Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq g g' hM hM' hgχ hg'χ (S := ∅)
    (fun p hp hpN _ => h p hp hpN)

/-- **Atkin–Li's twist theorem** (weight 2, trivial nebentypus, `(·/r)`, `r ≡ 1 mod 4`
squarefree prime to the level). -/
theorem atkinLiTwistNew : AtkinLiTwistNew :=
  atkinLiTwistNew_of_newformUniqueAcrossLevels newformUniqueAcrossLevels

/-- The leaf `HeckeThetaNewform` again, through Atkin–Li (gz-theta's route). -/
theorem heckeThetaNewform_via_atkinLi : ZInQ.GZDecomp.HeckeThetaNewform :=
  heckeThetaNewform_of_atkinLi atkinLiTwistNew

end ZInQ.GZTheta
