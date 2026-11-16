import ZInQKernel.OneProof.H.TailR
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.Smooth.RegularLocalRing

/-!
# Regular points are smooth over a perfect field (H-81 leaf `RegularSmoothPerfect`)

The `⇐` half of Stacks `00TV`, proved from results already in the tree:
`Algebra.FormallySmooth.localization_of_isRegularLocalRing`, vendored from
frenzymath/Jacobian-Challenge (commit `c4254cce15b3e284a0a3ae1d73936f2ee195d272`; authors Axel
Delaval, Jie Xu and Shitan Xu; see the LICENSE and NOTICE in
`ZInQKernel/Contrib/CloudW07JacobiansCurves/`), together with Mathlib's
`Algebra.FormallySmooth.of_perfectField` and `Algebra.IsSmoothAt.exists_notMem_smooth`
(Mathlib, `RingTheory/Smooth/Field.lean` and `RingTheory/Smooth/Locus.lean`, Andrew Yang).
-/

namespace ZInQ.Contrib.OneProof.RegularSmoothPerfect

set_option backward.isDefEq.respectTransparency false in
/-- **H-81 leaf `RegularSmoothPerfect`** (proved). If `S` is a finite type algebra over a perfect
field `k` and `S_q` is a regular local ring, then `S_q` is formally smooth over `k` (its residue
field is essentially of finite type over the perfect field `k`, hence formally smooth), so some
`g ∉ q` has `S_g` smooth over `k`. -/
theorem regularSmoothPerfect_proof : _root_.CurveSplit.RegularSmoothPerfect := by
  intro k _ _ S _ _ _ q _ hreg
  have : IsRegularLocalRing (Localization.AtPrime q) := hreg
  have : Algebra.FinitePresentation k S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
    inferInstanceAs (Algebra.EssFiniteType k (Localization.AtPrime q ⧸ _))
  have : Algebra.IsSmoothAt k q := Algebra.FormallySmooth.localization_of_isRegularLocalRing q
  exact Algebra.IsSmoothAt.exists_notMem_smooth k q

end ZInQ.Contrib.OneProof.RegularSmoothPerfect
