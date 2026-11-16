/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsLocalRing_mk_comp_algebraMap_surjective_of_maximalIdeal_le
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_IsLocalRing_mk_comp_algebraMap_surjective_of_maximalIdeal_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u v
theorem IsLocalRing.mk_comp_algebraMap_surjective_of_maximalIdeal_le
    {𝒪 : Type u} {A : Type v} [inst_t1 : CommRing 𝒪] [inst_t2 : IsLocalRing 𝒪] [inst_t3 : IsPrecomplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [inst_t4 : CommRing A] [inst_t5 : Algebra 𝒪 A] [inst_t6 : IsLocalRing A] [inst_t7 : IsNoetherianRing A]
    (hres : Function.Surjective (⇑(IsLocalRing.residue A) ∘ ⇑(algebraMap 𝒪 A)))
    {J : Ideal A}
    (hle : IsLocalRing.maximalIdeal A ≤
      J ⊔ IsLocalRing.maximalIdeal A ^ 2 ⊔ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) :
    Function.Surjective (⇑(Ideal.Quotient.mk J) ∘ ⇑(algebraMap 𝒪 A)) :=
  @_root_.P2MW.S_IsLocalRing_mk_comp_algebraMap_surjective_of_maximalIdeal_le.solution 𝒪 A inst_t1 inst_t2 inst_t3 inst_t4 inst_t5 inst_t6 inst_t7 hres J hle
