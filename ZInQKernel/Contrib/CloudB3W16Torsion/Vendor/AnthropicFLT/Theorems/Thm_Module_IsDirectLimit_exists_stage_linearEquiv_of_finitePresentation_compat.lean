/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Module_IsDirectLimit_exists_stage_linearEquiv_of_finitePresentation_compat. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Module_IsDirectLimit_exists_stage_linearEquiv_of_finitePresentation_compat

set_option backward.isDefEq.respectTransparency false

universe u v w
theorem Module.IsDirectLimit.exists_stage_linearEquiv_of_finitePresentation_compat
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {B₀ : Type u} [CommRing B₀]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra B₀ (B i)]
    (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) [DirectedSystem B (fun i j h => τ i j h)]
    (Bω : Type u) [CommRing Bω] [Algebra B₀ Bω] (g : ∀ i, B i →ₐ[B₀] Bω)
    (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i)
    (hsurj : ∀ b : Bω, ∃ i x, g i x = b)
    (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0)
    (i₀ : ι) [Algebra (B i₀) Bω] (hgi : ∀ x, algebraMap (B i₀) Bω x = g i₀ x)
    (P Q : Type w) [AddCommGroup P] [Module (B i₀) P] [AddCommGroup Q] [Module (B i₀) Q]
    [Module.FinitePresentation (B i₀) P] [Module.FinitePresentation (B i₀) Q]
    (e : TensorProduct (B i₀) Bω P ≃ₗ[Bω] TensorProduct (B i₀) Bω Q) :
    ∃ (j : ι) (hj : i₀ ≤ j) (gj : letI := (τ i₀ j hj).toRingHom.toAlgebra; B j →ₐ[B i₀] Bω) (_ : ∀ b, gj b = g j b)
      (ej : letI := (τ i₀ j hj).toRingHom.toAlgebra; TensorProduct (B i₀) (B j) P ≃ₗ[B j] TensorProduct (B i₀) (B j) Q),
      letI := (τ i₀ j hj).toRingHom.toAlgebra
      ∀ x : TensorProduct (B i₀) (B j) P, e (gj.toLinearMap.rTensor P x) = gj.toLinearMap.rTensor Q (ej x) := by p2m_exact_reverting @_root_.P2MW.S_Module_IsDirectLimit_exists_stage_linearEquiv_of_finitePresentation_compat.solution
