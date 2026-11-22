import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Finite surjections are surjective on algebraically closed field-valued points. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

private theorem exists_section_of_isFinite_over_algClosed {K : Type} [Field K] [IsAlgClosed K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) [IsFinite f] [Nonempty X] :
    ∃ x : Spec (CommRingCat.of K) ⟶ X, x ≫ f = 𝟙 _ := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let e := X.isoSpec
  let A := Γ(X, ⊤)
  let θ := Spec.preimage (e.inv ≫ f)
  have hθ : Spec.map θ = e.inv ≫ f := Spec.map_preimage _
  have hθfin : θ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hθ]
    infer_instance
  let _ : Algebra K A := θ.hom.toAlgebra
  have : Module.Finite K A := hθfin
  obtain ⟨x⟩ : Nonempty X := inferInstance
  let p : PrimeSpectrum A := e.hom x
  obtain ⟨M, hM, -⟩ := Ideal.ne_top_iff_exists_maximal.mp p.isPrime.ne_top
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  let φ : A →ₐ[K] K := (IsAlgClosed.lift : (A ⧸ M) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K M)
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ e.inv, ?_⟩
  rw [Category.assoc, ← hθ, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  exact φ.commutes a

theorem exists_lift_of_finite_surjective_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (y : Spec (CommRingCat.of K) ⟶ Y) :
    ∃ x : Spec (CommRingCat.of K) ⟶ X, x ≫ f = y := by
  have : Nonempty ↥(pullback f y : Scheme) :=
    ⟨((pullback.snd f y).surjective (IsLocalRing.closedPoint K)).choose⟩
  obtain ⟨x, hx⟩ := exists_section_of_isFinite_over_algClosed (pullback.snd f y)
  refine ⟨x ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hx, Category.id_comp]

end AlgebraicGeometry

#print axioms AlgebraicGeometry.exists_lift_of_finite_surjective_of_isAlgClosed
