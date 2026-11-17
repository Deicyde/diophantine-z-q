/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_constantFieldDescent_correspondence (git blob 39efc023a0e32282998ff74e0394675a5465ce9b, sha256 3b3defcc8541654b4019c8ce97ea86edf52bf94f6d5564cc6950e9fa7778ce8b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_constantFieldDescent_correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

universe u v w x

theorem AlgebraicCurve.exists_constantFieldDescent_correspondence
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ι : Type w} [Finite ι] (F' : ι → Type x) [∀ i, Field (F' i)] [∀ i, Algebra K (F' i)]
    (φ ψ : ∀ i, F →ₐ[K] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hfin : ∀ i, FiniteAlong K (ψ i)) :
    ∃ (K₀ : Type u) (F₀ : Type v) (F'₀ : ι → Type x)
      (_ : Field K₀) (_ : Field F₀) (_ : ∀ i, Field (F'₀ i))
      (_ : Algebra K₀ K) (_ : Algebra K₀ ℂ) (_ : IsAlgClosed K₀) (_ : Countable K₀)
      (_ : Algebra K₀ F₀) (_ : Algebra F₀ F) (_ : Algebra K₀ F)
      (_ : IsScalarTower K₀ K F) (_ : IsScalarTower K₀ F₀ F) (_ : IsCurveOver K₀ F₀)
      (_ : ∀ i, Algebra K₀ (F'₀ i)) (_ : ∀ i, Algebra (F'₀ i) (F' i)) (_ : ∀ i, Algebra K₀ (F' i))
      (_ : ∀ i, IsScalarTower K₀ K (F' i)) (_ : ∀ i, IsScalarTower K₀ (F'₀ i) (F' i))
      (_ : ∀ i, IsCurveOver K₀ (F'₀ i))
      (φ₀ ψ₀ : ∀ i, F₀ →ₐ[K₀] F'₀ i),
      (∃ x : F₀, Transcendental K₀ x ∧
        FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀) ∧
      IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ ∧
      (∀ i, ∃ x : F'₀ i, Transcendental K₀ x ∧
        FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set (F'₀ i))) (F'₀ i)) ∧
      (∀ i, IntermediateField.adjoin K (Set.range (algebraMap (F'₀ i) (F' i))) = ⊤) ∧
      (∀ i (f : F₀), φ i (algebraMap F₀ F f) = algebraMap (F'₀ i) (F' i) (φ₀ i f)) ∧
      (∀ i (f : F₀), ψ i (algebraMap F₀ F f) = algebraMap (F'₀ i) (F' i) (ψ₀ i f)) ∧
      (∀ i, FiniteAlong K₀ (φ₀ i)) ∧ (∀ i, FiniteAlong K₀ (ψ₀ i)) := by
  revert K F hfg ι F' φ ψ hφ hfin
  exact @_root_.P2MW.S_AlgebraicCurve_exists_constantFieldDescent_correspondence.solution
