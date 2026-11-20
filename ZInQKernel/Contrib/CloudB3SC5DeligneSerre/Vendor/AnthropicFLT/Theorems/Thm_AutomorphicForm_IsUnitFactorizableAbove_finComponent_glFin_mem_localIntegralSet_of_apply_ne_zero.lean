/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_IsUnitFactorizableAbove_finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero (git blob bd609bef4d05a2170f383d235868293be5f6b99a, sha256 6892eac3b7ad1f28b070582759cecf7a9247f39b8fd271bd8f0b375188986640).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_TwistedOrbital
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_IsUnitFactorizableAbove_finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero
    (K : Type) [Field K] [NumberField K]
    (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsUnitFactorizableAbove K K U S f)
    (z : GL (Fin 2) (AdeleRing (𝓞 K) K)) (hz : f z ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v := by
  revert K U S f hf z hz v hv
  exact @_root_.P2MW.S_AutomorphicForm_IsUnitFactorizableAbove_finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero.solution
