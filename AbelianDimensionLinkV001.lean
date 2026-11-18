import FibreDimensionV002
import ZInQKernel.Contrib.AbVarBC.Dim

/-!
# `dim A = dim B + r` with the abelian dimension read off `B`

The abelian quotient `B` has a natural-number dimension `a` (proved), so the dimension formula
takes the form: `dim A = a + r` where `a = dim B` and `r` is the rank of the natural torus
presentation of `ker π`.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NeronRelativeDimension

namespace SemiAbelianKernel

variable {K : Type} [Field K] {O : ValuationSubring K} {A : PkgI3.AbVar K}

/-- **`dim A = dim B + r`**: there is `a` with `dim B = a` and `dim A = a + r`. -/
theorem exists_dim_generic_of_presentation (hV1 : SmoothGroupRelDimLocal)
    (hV3 : SmoothRelDimKrullDim) (hHom : GroupSchemeDimStalk)
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom]
    (eA : (Over.pullback (jO O)).obj N ≅ A.X)
    {k : Type} [Field k] [IsAlgClosed k] (φ : O →+* k)
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U]
    (inc : U ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj N) [IsOpenImmersion inc.left]
    (B : PkgI3.AbVar k) (π : U ⟶ B.X) [IsMonHom π] [Flat π.left] (r : ℕ)
    {e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U)}
    (hnat : IsNatural r U e)
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (hker : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range) :
    ∃ a : ℕ, B.dim = (a : WithBot ℕ∞) ∧
      topologicalKrullDim A.X.left = ((a + r : ℕ) : WithBot ℕ∞) := by
  obtain ⟨a, ha⟩ := PkgI3.AbVar.dim_finite B
  exact ⟨a, ha, dim_generic_of_presentation hV1 hV3 hHom N eA φ U inc B π a r ha hnat he hker⟩

end SemiAbelianKernel
