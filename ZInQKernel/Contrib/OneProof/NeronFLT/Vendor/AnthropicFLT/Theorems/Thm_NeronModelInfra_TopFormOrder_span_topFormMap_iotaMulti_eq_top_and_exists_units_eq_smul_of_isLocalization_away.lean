/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_TopFormOrder_span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_TopFormOrder_span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away
    (R K B B' : Type u) [CommRing R] [CommRing K] [Algebra R K] (ϖ : R) [IsLocalization.Away ϖ K]
    [CommRing B] [Algebra R B] [CommRing B'] [Algebra B B'] [Algebra K B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R K B'] [IsLocalization.Away (algebraMap R B ϖ) B']
    (d : ℕ) (β : Module.Basis (Fin d) B (Ω[B⁄R])) :
    letI := moduleAlong B B' (⋀[B']^d (Ω[B'⁄K]))
    Submodule.span B' {topFormMap R K B B' d (exteriorPower.ιMulti B d β)} = ⊤ ∧
      ∀ σ : ⋀[B']^d (Ω[B'⁄K]), Submodule.span B' {σ} = ⊤ →
        ∃ u : B'ˣ, σ = (u : B') • topFormMap R K B B' d (exteriorPower.ιMulti B d β) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_TopFormOrder_span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away.solution
