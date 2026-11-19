/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport (git blob a3ca0e88ebc41f9d7c1594458bbaa31bbfec3332, sha256 18445fb0cae77095502a8de8a2848f9dcb9e63f0cb1eb133d56419d4e58481a8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory AutomorphicForm
open scoped Topology Pointwise

scoped instance (F : Type) [Field F] [NumberField F] : T2Space (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 F) F))

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))]
    (μ : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
    (ff g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hff : IsFinTestFactor F ff) (hgs : HasCompactSupport g) :
    IsFinTestFactor F (fun x => ∫ b, ff (x * b) * g b ∂μ) := by
  obtain ⟨hlc, hsupp⟩ := hff
  constructor
  ·
    obtain ⟨V, hV, hVf⟩ := hlc.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport hsupp
    have h1 : (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) ∈ V := mem_of_mem_nhds hV
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hnhds : (fun y => y * x⁻¹) ⁻¹' V ∈ 𝓝 x :=
      (continuous_mul_const x⁻¹).continuousAt.preimage_mem_nhds (by simpa using hV)
    filter_upwards [hnhds] with y hy
    show (∫ b, ff (y * b) * g b ∂μ) = ∫ b, ff (x * b) * g b ∂μ
    have hfun : (fun b => ff (y * b) * g b) = fun b => ff (x * b) * g b := by
      funext b
      have h := hVf (y * x⁻¹) hy 1 h1 (x * b)
      rw [mul_one, show y * x⁻¹ * (x * b) = y * b by simp only [mul_assoc, inv_mul_cancel_left]] at h
      rw [h]
    rw [hfun]
  ·
    refine HasCompactSupport.intro (hsupp.mul hgs.inv) fun x hx => ?_
    have hfun : (fun b => ff (x * b) * g b) = fun _ => 0 := by
      funext b
      by_contra hne
      have hgb : g b ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
      have hfb : ff (x * b) ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
      exact hx ⟨x * b, subset_tsupport _ (Function.mem_support.mpr hfb), b⁻¹,
        Set.inv_mem_inv.mpr (subset_tsupport _ (Function.mem_support.mpr hgb)), mul_inv_cancel_right x b⟩
    show (∫ b, ff (x * b) * g b ∂μ) = 0
    rw [hfun, integral_zero]
