/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_RingTheory_Sequence_IsWeaklyRegular_isZero_tor_one_quotient_ofList. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_RingTheory_Sequence_IsWeaklyRegular_isZero_tor_one_quotient_ofList

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

theorem RingTheory.Sequence.IsWeaklyRegular.isZero_tor_one_quotient_ofList
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    {rs : List R} (hM : RingTheory.Sequence.IsWeaklyRegular M rs) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (R ⧸ Ideal.ofList rs))).obj
      (ModuleCat.of R M)) := by p2m_exact_reverting @_root_.P2MW.S_RingTheory_Sequence_IsWeaklyRegular_isZero_tor_one_quotient_ofList.solution
