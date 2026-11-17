/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support (git blob 4b420a03dc057d65994a1546e9a978bc83f2aecd, sha256 dcec6d1caf187bbb729fa38d7ec135b802204e31ec69238df216b25e225c35e1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve

namespace P2MW.S_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support

set_option Elab.async false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place.exists_forall_ord_eq_finset Place Divisor Divisor.degZero Divisor.mem_degZero Divisor.principal Divisor.mem_principal HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective HasPrincipalDivisors.exists_divisor)
open _root_.AlgebraicCurve

namespace WC1bSolMV

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_mk_eq_forall_notMem [HasPrincipalDivisors K F]
    (x : Pic0 K F) (S : Finset (Place K F)) :
    ∃ D : Divisor.degZero (K := K) (F := F),
      Pic0.mk D = x ∧ ∀ v ∈ (D : Divisor K F).support, v ∉ S := by
  classical

  obtain ⟨D₀, hD₀⟩ := Pic0.mk_surjective x

  obtain ⟨g, hg0, hgord⟩ := AlgebraicCurve.Place.exists_forall_ord_eq_finset (K := K) S (fun v => (D₀ : Divisor K F) v)

  obtain ⟨E, hEord, hEdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) g hg0
  set E' : Divisor.degZero (K := K) (F := F) := ⟨E, Divisor.mem_degZero.mpr hEdeg⟩ with hE'
  have hEprin : E' ∈ (Divisor.principal (K := K) (F := F)).addSubgroupOf
      (Divisor.degZero (K := K) (F := F)) := by
    rw [AddSubgroup.mem_addSubgroupOf]
    exact Divisor.mem_principal.mpr ⟨g, hg0, fun v => hEord v⟩

  refine ⟨D₀ - E', ?_, ?_⟩
  · have hmkE : Pic0.mk E' = 0 := (QuotientAddGroup.eq_zero_iff E').mpr hEprin
    show QuotientAddGroup.mk (D₀ - E') = x
    rw [QuotientAddGroup.mk_sub, ← hD₀]
    show Pic0.mk D₀ - Pic0.mk E' = Pic0.mk D₀
    rw [hmkE, sub_zero]
  · intro v hv hvS
    refine (Finsupp.mem_support_iff.mp hv) ?_
    show (D₀ : Divisor K F) v - E v = 0
    rw [hEord v, hgord v hvS, sub_self]

end WC1bSolMV

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F] (x : Pic0 K F) (S : Finset (Place K F)) :
    ∃ D : Divisor.degZero (K := K) (F := F), Pic0.mk D = x ∧ ∀ v ∈ (D : Divisor K F).support, v ∉ S :=
  AlgebraicCurve.WC1bSolMV.exists_mk_eq_forall_notMem x S

end
