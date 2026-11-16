/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AdicCompletion_map_ker_subtype_injective_and_range_eq_ker_map
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AdicCompletion_map_ker_subtype_injective_and_range_eq_ker_map

set_option autoImplicit false

universe u

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] (ρ : M →ₗ[R] N) :
    Function.Injective (AdicCompletion.map I (LinearMap.ker ρ).subtype) ∧
      LinearMap.range (AdicCompletion.map I (LinearMap.ker ρ).subtype) =
        LinearMap.ker (AdicCompletion.map I ρ) := by
  refine ⟨AdicCompletion.map_injective I (LinearMap.ker ρ).injective_subtype, ?_⟩
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.surjective_rangeRestrict
  have hex : Function.Exact (LinearMap.ker ρ).subtype ρ.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have h1 : Function.Exact (AdicCompletion.map I (LinearMap.ker ρ).subtype)
      (AdicCompletion.map I ρ.rangeRestrict) :=
    AdicCompletion.map_exact (LinearMap.ker ρ).injective_subtype hex hsurj
  have h2 : Function.Injective (AdicCompletion.map I (LinearMap.range ρ).subtype) :=
    AdicCompletion.map_injective I (LinearMap.range ρ).injective_subtype
  have hfac : (LinearMap.range ρ).subtype ∘ₗ ρ.rangeRestrict = ρ := by
    ext x; rfl
  have h3 : AdicCompletion.map I ρ =
      AdicCompletion.map I (LinearMap.range ρ).subtype ∘ₗ AdicCompletion.map I ρ.rangeRestrict := by
    first
      | (rw [AdicCompletion.map_comp, hfac])
      | (rw [← AdicCompletion.map_comp, hfac])
  rw [h3, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr h2)]
  exact (h1.linearMap_ker_eq).symm
