/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_comp_add_right_mem_pureTensorSet (git blob 59b809b68f3b62fb02db89a76761f91dd2878f6f, sha256 3ee6fbc22b3127737815bccf7d75bfd3e25a699ca977c3a0a231ea36f9297d3c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_comp_add_right_mem_pureTensorSet

open NumberField NumberField.AdelicFourier
open scoped SchwartzMap Classical

theorem solution
    {F : Type*} [Field F] [NumberField F] (y : AdeleRing (𝓞 F) F)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x => f (x + y)) ∈ pureTensorSet F := by
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hf
  set c := InfiniteAdeleRing.ringEquiv_mixedSpace F y.1
  have hTG : Function.HasTemperateGrowth (fun z : mixedEmbedding.mixedSpace F => z + c) :=
    Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const c)
  have hUp : ∃ (k : ℕ) (C : ℝ), ∀ z : mixedEmbedding.mixedSpace F,
      ‖z‖ ≤ C * (1 + ‖z + c‖) ^ k := by
    refine ⟨1, 1 + ‖c‖, fun z => ?_⟩
    have h1 : ‖z‖ ≤ ‖z + c‖ + ‖c‖ := by
      have := norm_add_le (z + c) (-c); simp only [add_neg_cancel_right, norm_neg] at this
      exact this
    nlinarith [norm_nonneg (z + c), norm_nonneg c]
  refine ⟨SchwartzMap.compCLM ℝ hTG hUp g, fun z => h (z + y.2),
    hlc.comp_continuous (continuous_add_const y.2),
    hcs.comp_homeomorph (Homeomorph.addRight y.2), ?_⟩
  funext x

  simp only [SchwartzMap.compCLM_apply, Function.comp_apply]
  congr 1
  rw [show (x + y).1 = x.1 + y.1 from rfl]
  exact congrArg g (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) x.1 y.1)
