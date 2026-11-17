/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_exists_forall_smoothnessDefect_le_of_smooth_pullback_snd
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_SmoothnessDefect
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_exists_forall_smoothnessDefect_le_of_smooth_pullback_snd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.exists_forall_smoothnessDefect_le_of_smooth_pullback_snd
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ c : ℕ, ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
      ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
        smoothnessDefect f x.1 ≤ c := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_forall_smoothnessDefect_le_of_smooth_pullback_snd.solution
