import ZInQKernel.Contrib.CloudR2Poincare.L4.B3Interface
import ZInQKernel.Contrib.CloudR2Poincare.L4.StabilizerScheme
import ZInQKernel.Contrib.CloudR2Poincare.L4.QuotientGeometry
import ZInQKernel.Contrib.CloudR2Poincare.L4.QuotientFiniteType
import ZInQKernel.Contrib.CloudR2Poincare.L3.Cartier

/-!
# B3: the actual finite-flat stabilizer quotient is an abelian variety

The only upstream quotient input is explicitly labelled
`FiniteStabilizerQuotientExists`. Every downstream group law, properness,
finite-type descent, Cartier smoothness, geometric integrality and dimension
comparison is proved. Finiteness of the ORIGINAL stabilizer is supplied exactly
by the (A) argument already in the agreed consumer telescope.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 100000
set_option maxRecDepth 300

variable {k : Type} [Field k] (A : PkgI3.AbVar k) (L : A.X.left.Pic)
    (H : L1.FiniteStabilizerScheme A L) (Q : L1.StabilizerQuotient A L H)

/-- Properness is proved, not part of the supplied quotient record. -/
theorem quotient_proper : IsProper Q.Q.hom := by
  haveI : IsSeparated Q.Q.hom := quotient_separated A L H Q
  haveI : LocallyOfFiniteType Q.Q.hom := locallyFiniteType_of_finite_flat_surjective Q.q
  haveI : UniversallyClosed (Q.q.left ≫ Q.Q.hom) := by rw [Over.w]; infer_instance
  haveI : UniversallyClosed Q.Q.hom := UniversallyClosed.of_comp_surjective Q.q.left Q.Q.hom
  exact {}

/-- Smoothness follows from the proved descended group object and L3's actual Cartier theorem. -/
theorem quotient_smooth [CharZero k] : Smooth Q.Q.hom := by
  letI := quotientGrp A L H Q
  exact L3.cartierSmooth_proof k Q.Q (locallyFiniteType_of_finite_flat_surjective Q.q)

/-- The actual quotient scheme, with its proved descended structure, as a PkgI3 abelian variety. -/
def quotientAbVar [CharZero k] : PkgI3.AbVar k where
  X := Q.Q
  grp := quotientGrp A L H Q
  proper := quotient_proper A L H Q
  smooth := quotient_smooth A L H Q
  geomInt := quotient_geometricallyIntegral A L H Q

/-- The literal quotient arrow, packaged as an actual abelian-variety homomorphism. -/
def quotientAbVarHom [CharZero k] : PkgI3.AbVar.Hom A (quotientAbVar A L H Q) :=
  letI := quotientGrp A L H Q
  haveI := quotient_isMonHom A L H Q
  PkgI3.AbVar.Hom.mk' Q.q

@[simp] theorem quotientAbVarHom_hom [CharZero k] :
    (quotientAbVarHom A L H Q).hom = Q.q := rfl

/-- The actual quotient dimension equals the original abelian-variety dimension. -/
theorem quotientAbVar_dim [CharZero k] : (quotientAbVar A L H Q).dim = A.dim :=
  quotient_dim_eq A L H Q

include Q in
/-- Every supplied stabilizer quotient gives the exact B4-consumed abelian-variety quotient data. -/
theorem abVarQuotient_of_stabilizerQuotient [CharZero k] :
    ∃ (D : PkgI3.AbVar k) (q : PkgI3.AbVar.Hom A D),
      Flat q.hom.left ∧ IsFinite q.hom.left ∧ Surjective q.hom.left ∧
      LocallyOfFinitePresentation q.hom.left ∧
      IsPullback ((fst H.K A.X ≫ H.j) * snd H.K A.X) (snd H.K A.X) q.hom q.hom ∧
      D.dim = A.dim := by
  refine ⟨quotientAbVar A L H Q, quotientAbVarHom A L H Q, ?_⟩
  simp only [quotientAbVarHom_hom]
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, Q.kernelPair,
    quotientAbVar_dim A L H Q⟩

/-- B3 downstream proof. Quotient existence is the SOLE explicitly labelled upstream input;
(A) remains the ordinary hA argument in the EXACT agreed consumer Prop. -/
theorem stabilizerAbVarQuotientExists_of_quotient
    (hQuotient : FiniteStabilizerQuotientExists) : StabilizerAbVarQuotientExists := by
  intro hA k _ _ B M hM
  letI : M.IsInvertible := hM.isInvertible
  let L := Scheme.Pic.mk M
  have hfin : IsFinite (L2.globalNormalizedKernel B L).hom :=
    L2.isFinite_globalNormalizedKernel_of_globalSeesaw hA B M hM
  let H := originalFiniteStabilizer B L hfin
  obtain ⟨Q⟩ := hQuotient B L H
  obtain ⟨D, q, hq⟩ := abVarQuotient_of_stabilizerQuotient B L H Q
  exact ⟨H, D, q, hq⟩

end ZInQ.Contrib.CloudR2Poincare.L4
