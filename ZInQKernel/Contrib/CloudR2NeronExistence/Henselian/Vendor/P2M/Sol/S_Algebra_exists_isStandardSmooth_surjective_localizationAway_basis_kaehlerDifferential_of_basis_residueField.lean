import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_Algebra_exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField.lean
Original Git blob: 45640ee40317ab62a841765979ca0512c83988cf
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_Algebra_FinitePresentation_exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_MvPolynomial_exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "KaehlerDifferential MvPolynomial TensorProduct"
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_Algebra_exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct KaehlerDifferential MvPolynomial

universe u

namespace MinimalAmbient
h77_bridge_namespace

theorem main
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (u : Ideal S) [u.IsPrime]
    {ι : Type} [Finite ι] (w : ι → S)
    (b₀ : Module.Basis ι u.ResidueField (u.ResidueField ⊗[S] Ω[S⁄R]))
    (hb₀ : ∀ i, b₀ i = (1 : u.ResidueField) ⊗ₜ[S] D R S (w i)) :
    ∃ (g : S) (_ : g ∉ u) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.IsStandardSmooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (W : ι → C) (b : Module.Basis ι C Ω[C⁄R]),
        (∀ i, algebraMap C (Localization.Away g) (W i) = algebraMap S (Localization.Away g) (w i)) ∧
        (∀ i, b i = D R C (W i)) := by
  obtain ⟨m, x, h, hsurj, hh, hdet⟩ :=
    Algebra.FinitePresentation.exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField u w b₀ hb₀
  set Δ : MvPolynomial (ι ⊕ Fin m) R := Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)) with hΔ
  set g : S := MvPolynomial.aeval (Sum.elim w x) Δ with hg
  obtain ⟨C, _, _, φ, hsm, hφh, hφΔ, huniv, b, hb⟩ :=
    MvPolynomial.exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential h

  let Sg := Localization.Away g
  let ψ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] Sg :=
    (IsScalarTower.toAlgHom R S Sg).comp (MvPolynomial.aeval (Sum.elim w x))
  have hψ : ∀ p, ψ p = algebraMap S Sg (MvPolynomial.aeval (Sum.elim w x) p) := fun p => rfl
  have hψh : ∀ a, ψ (h a) = 0 := fun a => by rw [hψ, hh a, map_zero]
  have hψΔ : IsUnit (ψ Δ) := by
    rw [hψ]
    exact IsLocalization.Away.algebraMap_isUnit (S := Sg) g
  obtain ⟨χ, hχ⟩ := huniv Sg ψ hψh hψΔ
  letI : Algebra C Sg := χ.toRingHom.toAlgebra
  haveI : IsScalarTower R C Sg := IsScalarTower.of_algebraMap_eq fun r => (χ.commutes r).symm
  refine ⟨g, hdet, C, inferInstance, inferInstance, inferInstance, inferInstance, hsm, ?_,
    fun i => φ (MvPolynomial.X (Sum.inl i)), b, ?_, hb⟩
  ·
    intro z
    obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) z
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp t.2
    obtain ⟨p, rfl⟩ := hsurj s
    obtain ⟨v, hv⟩ := hφΔ
    refine ⟨φ p * ((v⁻¹ : Cˣ) : C) ^ k, ?_⟩
    change χ (φ p * ((v⁻¹ : Cˣ) : C) ^ k) = _
    rw [IsLocalization.eq_mk'_iff_mul_eq, map_mul, map_pow]
    have h1 : χ (φ p) = algebraMap S Sg (MvPolynomial.aeval (Sum.elim w x) p) := by
      rw [← hψ, ← hχ]; rfl
    have h2 : χ ((v⁻¹ : Cˣ) : C) * algebraMap S Sg g = 1 := by
      have : χ (v : C) = algebraMap S Sg g := by rw [hv, ← hψ Δ, ← hχ]; rfl
      rw [← this, ← map_mul, Units.inv_mul, map_one]
    rw [h1, ← hk, map_pow, mul_assoc, ← mul_pow, h2, one_pow, mul_one]
  · intro i
    change χ (φ (MvPolynomial.X (Sum.inl i))) = _
    rw [show χ (φ (MvPolynomial.X (Sum.inl i))) = ψ (MvPolynomial.X (Sum.inl i)) by rw [← hχ]; rfl, hψ,
      MvPolynomial.aeval_X, Sum.elim_inl]

end MinimalAmbient

theorem solution
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (u : Ideal S) [u.IsPrime]
    {ι : Type} [Finite ι] (w : ι → S)
    (b₀ : Module.Basis ι u.ResidueField (u.ResidueField ⊗[S] Ω[S⁄R]))
    (hb₀ : ∀ i, b₀ i = (1 : u.ResidueField) ⊗ₜ[S] D R S (w i)) :
    ∃ (g : S) (_ : g ∉ u) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.IsStandardSmooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (W : ι → C) (b : Module.Basis ι C Ω[C⁄R]),
        (∀ i, algebraMap C (Localization.Away g) (W i) = algebraMap S (Localization.Away g) (w i)) ∧
        (∀ i, b i = D R C (W i)) :=
  MinimalAmbient.main u w b₀ hb₀


end P2MW.S_Algebra_exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
