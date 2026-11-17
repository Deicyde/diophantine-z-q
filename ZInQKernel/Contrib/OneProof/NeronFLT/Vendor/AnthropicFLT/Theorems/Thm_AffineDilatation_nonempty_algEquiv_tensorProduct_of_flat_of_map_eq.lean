/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AffineDilatation_nonempty_algEquiv_tensorProduct_of_flat_of_map_eq
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_RingTheory_AffineDilatation
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AffineDilatation_nonempty_algEquiv_tensorProduct_of_flat_of_map_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open TensorProduct

universe u

theorem AffineDilatation.nonempty_algEquiv_tensorProduct_of_flat_of_map_eq
    {P : Type u} [CommRing P] (I : Ideal P) (a : P) (ha : a ∈ I)
    {C : Type u} [CommRing C] [Algebra P C] [Module.Flat P C]
    (J : Ideal C) (b : C) (hJ : I.map (algebraMap P C) = J) (hb : algebraMap P C a = b) :
    ∃ e : C ⊗[P] AffineDilatation.Ring I a ≃ₐ[C] AffineDilatation.Ring J b,
      ∀ (g : P) (hg : g ∈ I),
        e (1 ⊗ₜ AffineDilatation.divElem I a g hg) =
          AffineDilatation.divElem J b (algebraMap P C g) (hJ ▸ Ideal.mem_map_of_mem (algebraMap P C) hg) := by p2m_exact_reverting @_root_.P2MW.S_AffineDilatation_nonempty_algEquiv_tensorProduct_of_flat_of_map_eq.solution
