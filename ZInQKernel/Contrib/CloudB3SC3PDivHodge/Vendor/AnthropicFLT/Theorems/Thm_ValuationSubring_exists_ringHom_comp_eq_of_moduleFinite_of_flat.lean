/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_exists_ringHom_comp_eq_of_moduleFinite_of_flat
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_ringHom_comp_eq_of_moduleFinite_of_flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.exists_ringHom_comp_eq_of_moduleFinite_of_flat
    {R : Type*} [inst_t1 : CommRing R] {B : Type*} [inst_t2 : CommRing B] [inst_t3 : Algebra R B]
    [inst_t4 : Module.Finite R B] [inst_t5 : Module.Flat R B]
    {K : Type*} [inst_t6 : Field K] [inst_t7 : IsAlgClosed K] (O : ValuationSubring K) [inst_t8 : Algebra R ↥O]
    {k : Type*} [inst_t9 : Field k] (π : ↥O →+* k) (hπ : Function.Surjective π)
    (φ₀ : B →+* k) (hcomp : φ₀.comp (algebraMap R B) = π.comp (algebraMap R ↥O)) :
    ∃ φ : B →+* ↥O, φ.comp (algebraMap R B) = algebraMap R ↥O ∧ π.comp φ = φ₀ :=
  @_root_.P2MW.S_ValuationSubring_exists_ringHom_comp_eq_of_moduleFinite_of_flat.solution R inst_t1 B inst_t2 inst_t3 inst_t4 inst_t5 K inst_t6 inst_t7 O inst_t8 k inst_t9 π hπ φ₀ hcomp
