/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [IsProper y] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (hA : ringKrullDim A = 1) (φ : Spec (CommRingCat.of A) ⟶ Y)
    (hφ : φ ≫ y = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (_ : IsProper c)
      (_ : SmoothOfRelativeDimension 1 c) (_ : IsIntegral C) (ψ : C ⟶ Y), ψ ≫ y = c ∧
      ∀ a : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A),
        a ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _ →
        ∃ p : Spec (CommRingCat.of k) ⟶ C, p ≫ c = 𝟙 _ ∧ p ≫ ψ = a ≫ φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one.solution
