/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn (git blob 1f2818a350b3b089cf096b34a5f63b3df496fe31, sha256 045af2211834787a0a81227e2382f7dc62387a3cf4e78f53af2b260cd6e54783).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn

open NumberField
open scoped Classical
open IsDedekindDomain AutomorphicForm

namespace TierTranslate

private theorem archEntries_mul (K : Type) [Field K] (a h : GL (Fin 2) (InfiniteAdeleRing K)) (i j : Fin 2) :
    archEntries K (a * h) i j = ∑ k : Fin 2, archEntries K a i k * archEntries K h k j := by
  simp only [archEntries_apply, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]

private theorem isArchTestFactor_comp_mul_left (K : Type) [Field K] [NumberField K]
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (hfa : IsArchTestFactor K fa)
    (a : GL (Fin 2) (InfiniteAdeleRing K)) : IsArchTestFactor K (fun h => fa (a * h)) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa
  refine ⟨⟨fun X => Φ (fun i j => ∑ k : Fin 2, archEntries K a i k * X k j), ?_, ?_⟩, ?_⟩
  · exact hΦ.comp (by fun_prop)
  · intro h
    show fa (a * h) = Φ (fun i j => ∑ k : Fin 2, archEntries K a i k * archEntries K h k j)
    rw [hfaΦ]
    congr 1
    funext i j
    exact archEntries_mul K a h i j
  · exact hsupp.comp_homeomorph (Homeomorph.mulLeft a)

private theorem isFinTestFactor_comp_mul_left (K : Type) [Field K] [NumberField K]
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (hff : IsFinTestFactor K ff)
    (b : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : IsFinTestFactor K (fun h => ff (b * h)) :=
  ⟨hff.1.comp_continuous (continuous_const_mul b), hff.2.comp_homeomorph (Homeomorph.mulLeft b)⟩

end TierTranslate

open TierTranslate in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hf : IsFactorizableTestFn K f)
    (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    IsFactorizableTestFn K (fun y => f (t⁻¹ * y)) := by
  obtain ⟨fa, ff, hfa, hff, hfx⟩ := hf
  refine ⟨fun h => fa (AdelicLevel.glArch (𝓞 K) K t⁻¹ * h),
    fun h => ff (AdelicLevel.glFin (𝓞 K) K t⁻¹ * h),
    isArchTestFactor_comp_mul_left K hfa _, isFinTestFactor_comp_mul_left K hff _, ?_⟩
  intro y
  show f (t⁻¹ * y) = fa (AdelicLevel.glArch (𝓞 K) K t⁻¹ * AdelicLevel.glArch (𝓞 K) K y) *
    ff (AdelicLevel.glFin (𝓞 K) K t⁻¹ * AdelicLevel.glFin (𝓞 K) K y)
  rw [hfx (t⁻¹ * y), map_mul (AdelicLevel.glArch (𝓞 K) K) t⁻¹ y,
    map_mul (AdelicLevel.glFin (𝓞 K) K) t⁻¹ y]
