/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_mem_of_isProper_of_forall_smoothProperCurve_mem. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_mem_of_isProper_of_forall_smoothProperCurve_mem

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.mem_of_isProper_of_forall_smoothProperCurve_mem
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [IsProper y] [IsIntegral Y]
    (S : Set (Spec (CommRingCat.of k) ⟶ Y))
    (y₀ : Spec (CommRingCat.of k) ⟶ Y) (hy₀ : y₀ ≫ y = 𝟙 _) (h₀ : y₀ ∈ S)
    (hS : ∀ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c]
      [SmoothOfRelativeDimension 1 c] [IsIntegral C] (ψ : C ⟶ Y), ψ ≫ y = c →
      ∀ p q : Spec (CommRingCat.of k) ⟶ C, p ≫ c = 𝟙 _ → q ≫ c = 𝟙 _ → p ≫ ψ ∈ S → q ≫ ψ ∈ S)
    (y₁ : Spec (CommRingCat.of k) ⟶ Y) (hy₁ : y₁ ≫ y = 𝟙 _) : y₁ ∈ S := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_mem_of_isProper_of_forall_smoothProperCurve_mem.solution
