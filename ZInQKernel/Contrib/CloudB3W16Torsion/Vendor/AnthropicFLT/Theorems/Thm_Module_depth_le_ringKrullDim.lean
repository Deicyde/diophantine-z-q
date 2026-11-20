/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Module_depth_le_ringKrullDim. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_Patching_SystemTypes
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Support
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Module_depth_le_ringKrullDim

set_option backward.isDefEq.respectTransparency false

theorem Module.depthFLT_le_ringKrullDim {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Nontrivial M] [Module.Finite R M] :
    .some (Module.depthFLT R M) ≤ ringKrullDim R := by p2m_exact_reverting @_root_.P2MW.S_Module_depth_le_ringKrullDim.solution
