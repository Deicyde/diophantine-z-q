/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open TensorProduct KaehlerDifferential

universe u

theorem Algebra.exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [Algebra.Smooth k B]
    {B' : Type u} [CommRing B'] [Algebra k B'] (ψ : B →ₐ[k] B') (hψ : Function.Surjective ψ)
    (v' : Ideal B') [v'.IsPrime] (v : Ideal B) [v.IsPrime] (hv' : v'.comap ψ.toRingHom = v)
    (hsm : Algebra.IsSmoothAt k v')
    (hrank : Module.finrank v.ResidueField (v.ResidueField ⊗[B] Ω[B⁄k]) ≤
      Module.finrank v'.ResidueField (v'.ResidueField ⊗[B'] Ω[B'⁄k])) :
    ∃ t : B, t ∉ v ∧ (RingHom.ker ψ.toRingHom).map (algebraMap B (Localization.Away t)) = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le.solution
