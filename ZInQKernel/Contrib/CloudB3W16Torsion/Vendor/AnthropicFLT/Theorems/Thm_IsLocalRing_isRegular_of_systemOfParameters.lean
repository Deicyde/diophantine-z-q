/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_IsLocalRing_isRegular_of_systemOfParameters. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_Patching_SystemTypes
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_IsLocalRing_isRegular_of_systemOfParameters

set_option backward.isDefEq.respectTransparency false

open IsLocalRing RingTheory
theorem IsLocalRing.isRegular_of_systemOfParameters
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hCM : (Module.depth R R : WithBot ℕ∞) = ringKrullDim R)
    {d : ℕ} (hdim : ringKrullDim R = d)
    (xs : List R) (hlen : xs.length = d) (hmem : ∀ y ∈ xs, y ∈ maximalIdeal R)
    (hsop : ringKrullDim (R ⧸ Ideal.ofList xs) = 0) :
    RingTheory.Sequence.IsRegular R xs := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isRegular_of_systemOfParameters.solution
