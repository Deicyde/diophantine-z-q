import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_Algebra_exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span.lean
Original Git blob: e0dae8929a08985fafffa9838ae80153e4820496
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_Algebra_exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "KaehlerDifferential TensorProduct"
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct KaehlerDifferential

universe u

theorem Algebra.exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (J : Ideal A) (hπJ : algebraMap R A π ∈ J)
    [Algebra (IsLocalRing.ResidueField R) (A ⧸ J)] [IsScalarTower R (IsLocalRing.ResidueField R) (A ⧸ J)]
    (𝔭 : Ideal A) [𝔭.IsPrime]
    (𝔮 : Ideal (A ⧸ J)) [𝔮.IsPrime] (h𝔮 : 𝔮.comap (Ideal.Quotient.mk J) = 𝔭)
    (hsmooth : Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮)
    (hfree : (⟨𝔮, ‹_›⟩ : PrimeSpectrum (A ⧸ J)) ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R])) :
    ∃ (g : A) (_ : g ∉ 𝔭) (r n : ℕ) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.Smooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (y : Fin r → C) (z : Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R]),
        (∀ i, b (Sum.inl i) = D R C (y i)) ∧ (∀ j, b (Sum.inr j) = D R C (z j)) ∧
        Ideal.comap (algebraMap C (Localization.Away g)) (J.map (algebraMap A (Localization.Away g))) =
          Ideal.span (insert (algebraMap R C π) (Set.range z)) ∧
        LinearIndependent (C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z)))
          fun j : Fin n => (1 : C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z))) ⊗ₜ[C]
            D R (Localization.Away g) (algebraMap C (Localization.Away g) (z j)) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_Algebra_exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
