/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_exists_specializes_fst_eq_snd_eq_of_specializes_snd
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_exists_specializes_fst_eq_snd_eq_of_specializes_snd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem NeronModelInfra.exists_specializes_fst_eq_snd_eq_of_specializes_snd
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (θ : ↑(pullback f f)) (hθ : f.base ((pullback.fst f f).base θ) = IsLocalRing.closedPoint R)
    (y : X) (hy : y ⤳ (pullback.snd f f).base θ) (hys : f.base y = IsLocalRing.closedPoint R) :
    ∃ θ' : ↑(pullback f f), θ' ⤳ θ ∧ (pullback.fst f f).base θ' = (pullback.fst f f).base θ ∧
      (pullback.snd f f).base θ' = y := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_specializes_fst_eq_snd_eq_of_specializes_snd.solution
