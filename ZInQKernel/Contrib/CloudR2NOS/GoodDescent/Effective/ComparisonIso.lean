/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Actual comparison of two effective outputs of the SAME fpqc scheme
coequalizer, used for original generic-fibre transport. It constructs the
map AND inverse with the real source morphism-descent theorem and proves
inverse equations by actual uniqueness, not an assumed generic iso.
Input cartesian/coequalizer data here are intermediate OUTPUTS of the
constructed tensor/Proj and original generic comparison diagrams.
-/
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- Construct a unique comparison isomorphism between two real cartesian
    coequalizer outputs, retaining their actual cover maps. -/
theorem exists_comparisonIso_of_fpqc_coequalizers
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R']
    {X Y U U₂ : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (u : U ⟶ Spec (CommRingCat.of R')) (qx : U ⟶ X) (qy : U ⟶ Y)
    (hqx : IsPullback qx u f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (hqy : IsPullback qy u g (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (u₂ : U₂ ⟶ Spec (CommRingCat.of (R' ⊗[R] R'))) (a₁ a₂ : U₂ ⟶ U)
    (ha₁ : IsPullback a₁ u₂ u (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] R').toRingHom)))
    (ha₂ : IsPullback a₂ u₂ u (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R').toRingHom)))
    (hx : a₁ ≫ qx = a₂ ≫ qx) (hy : a₁ ≫ qy = a₂ ≫ qy) :
    ∃ i : X ≅ Y, qx ≫ i.hom = qy ∧ qy ≫ i.inv = qx ∧ i.hom ≫ g = f := by
  let ex := ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
    f u qx hqx u₂ a₁ a₂ ha₁ ha₂ hx qy hy
  obtain ⟨α, hα, _⟩ := ex
  let ey := ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
    g u qy hqy u₂ a₁ a₂ ha₁ ha₂ hy qx hx
  obtain ⟨β, hβ, _⟩ := ey
  have eXX : ∃! z : X ⟶ X, qx ≫ z = qx :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
      f u qx hqx u₂ a₁ a₂ ha₁ ha₂ hx qx hx
  have eYY : ∃! z : Y ⟶ Y, qy ≫ z = qy :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
      g u qy hqy u₂ a₁ a₂ ha₁ ha₂ hy qy hy
  have hαβ : α ≫ β = 𝟙 X := eXX.unique (by rw [← Category.assoc, hα, hβ]) (by simp)
  have hβα : β ≫ α = 𝟙 Y := eYY.unique (by rw [← Category.assoc, hβ, hα]) (by simp)
  have hbase : a₁ ≫ (qx ≫ f) = a₂ ≫ (qx ≫ f) := by
    simpa only [Category.assoc] using congrArg (· ≫ f) hx
  have eBase : ∃! z : X ⟶ Spec (CommRingCat.of R), qx ≫ z = qx ≫ f :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
      f u qx hqx u₂ a₁ a₂ ha₁ ha₂ hx (qx ≫ f) hbase
  have hfg : α ≫ g = f := eBase.unique (by
    rw [← Category.assoc, hα, hqy.w, hqx.w]) rfl
  exact ⟨⟨α, β, hαβ, hβα⟩, hα, hβ, hfg⟩

#print axioms exists_comparisonIso_of_fpqc_coequalizers

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
