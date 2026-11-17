/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub (git blob a52e610664907db2414e65c4fe011ee517b198ea, sha256 55100fe4cc2c4e0e4b5feec4247e49a4038b8e7688d57853eb9989b60f144f56).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_WeilDatum
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_evalFun_add
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_evalFun_mul
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_evalFun_ne_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_evalFun_zsmul
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_evalFun_zpow_left
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_mem_of_ord_nonneg
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_WeilDatum_symm_pairing
import Batteries.Tactic.Alias

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace AlgebraicCurve.WeilDatum
end AlgebraicCurve.WeilDatum
namespace P2MW.S_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub.AlgebraicCurve
end P2MW.S_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub.AlgebraicCurve

namespace P2MW.S_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub

set_option Elab.async false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
export _root_.AlgebraicCurve (WeilDatum Place.IsRational Divisor.evalFun Divisor.evalFun_def WeilReciprocity Place Place.ord_inv Place.ord_zpow Divisor Divisor.degree Divisor.degZero Divisor.mem_degZero Divisor.IsPrincipal Divisor.principal Divisor.mem_principal HasPrincipalDivisors Pic0 Pic0.mk Pic0.torsion Pic0.mem_torsion HasPrincipalDivisors.exists_divisor Pic0.torsion.exists_forall_ord_eq_mul Divisor.evalFun_add Divisor.evalFun_mul Divisor.evalFun_ne_zero Divisor.evalFun_zsmul Divisor.evalFun_zpow_left Place.evalAt_algebraMap Place.isRational_iff_deg_eq_one WeilDatum.symm_pairing)
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem prod_zpow_eq_zpow_sum_i {c : K} (hc : c ≠ 0) {ι : Type*} (s : Finset ι)
    (m : ι → ℤ) : ∏ i ∈ s, c ^ m i = c ^ (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hc, ih]

private theorem support_zsmul_subset_i (c : ℤ) (D : Divisor K F) :
    ((c • D : Divisor K F)).support ⊆ D.support := by
  intro v hv
  rw [Finsupp.mem_support_iff] at hv ⊢
  intro h0
  exact hv (by rw [Finsupp.smul_apply, h0, smul_zero])

private theorem isPrincipal_neg_i {D : Divisor K F} (h : Divisor.IsPrincipal D) :
    Divisor.IsPrincipal (-D) := by
  obtain ⟨g, hg0, hg⟩ := h
  refine ⟨g⁻¹, inv_ne_zero hg0, fun v => ?_⟩
  rw [Finsupp.neg_apply, Place.ord_inv, ← hg v]

private theorem isPrincipal_add_i {A B : Divisor K F} (hA : Divisor.IsPrincipal A)
    (hB : Divisor.IsPrincipal B) : Divisor.IsPrincipal (A + B) := by
  obtain ⟨f, hf0, hfv⟩ := hA
  obtain ⟨g, hg0, hgv⟩ := hB
  refine ⟨f * g, mul_ne_zero hf0 hg0, fun v => ?_⟩
  rw [Finsupp.add_apply, hfv v, hgv v, v.ord_mul hf0 hg0]

private theorem isPrincipal_sub_of_mk_eq_i {A B : Divisor.degZero (K := K) (F := F)}
    (h : Pic0.mk A = Pic0.mk B) :
    Divisor.IsPrincipal ((A : Divisor K F) - (B : Divisor K F)) := by
  have hsub0 : Pic0.mk (A - B) = 0 := by
    show QuotientAddGroup.mk (A - B) = 0
    rw [QuotientAddGroup.mk_sub, sub_eq_zero]
    exact h
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp hsub0
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  have hcoe : ((A - B : Divisor.degZero (K := K) (F := F)) : Divisor K F)
      = (A : Divisor K F) - (B : Divisor K F) := rfl
  rw [hcoe] at hmem
  exact Divisor.mem_principal.mp hmem

private theorem evalFun_algebraMap_of_degree_eq_zero_i {c : K} (hc : c ≠ 0) {D : Divisor K F}
    (hdeg : Divisor.degree D = 0) (hrat : ∀ v ∈ D.support, Place.IsRational v) :
    Divisor.evalFun (algebraMap K F c) D = 1 := by
  classical
  rw [Divisor.evalFun_def]
  have hfac : ∀ v ∈ D.support, v.evalAt (algebraMap K F c) ^ D v = c ^ D v := fun v _ => by
    rw [Place.evalAt_algebraMap]
  rw [Finset.prod_congr rfl hfac, prod_zpow_eq_zpow_sum_i hc]
  have hsum : ∑ v ∈ D.support, D v = 0 := by
    have h1 : Divisor.degree D = D.sum fun v m => m * (v.deg : ℤ) :=
      Finsupp.liftAddHom_apply _ _
    have h2 : D.sum (fun v m => m * (v.deg : ℤ)) = ∑ v ∈ D.support, D v := by
      refine Finset.sum_congr rfl fun v hv => ?_
      show D v * (v.deg : ℤ) = D v
      rw [(Place.isRational_iff_deg_eq_one v).mp (hrat v hv), Nat.cast_one, mul_one]
    rw [← h2, ← h1, hdeg]
  rw [hsum, zpow_zero]

namespace WeilDatum
export _root_.AlgebraicCurve.WeilDatum (pairing symm f₁ ord_f₁ D₁ f₁_ne_zero mk disjoint ord_f₂ D₂ f₂_ne_zero f₂ rational symm_pairing)
open _root_.AlgebraicCurve.WeilDatum

variable {n : ℕ}

private theorem _root_.AlgebraicCurve.WeilDatum.isPrincipal_smul_left_i (d : WeilDatum K F n) :
    Divisor.IsPrincipal ((n : ℤ) • d.D₁) :=
  ⟨d.f₁, d.f₁_ne_zero, fun v => by rw [Finsupp.smul_apply, smul_eq_mul, d.ord_f₁ v]⟩

alias isPrincipal_smul_left_i := _root_.AlgebraicCurve.WeilDatum.isPrincipal_smul_left_i
private theorem _root_.AlgebraicCurve.WeilDatum.isPrincipal_smul_right_i (d : WeilDatum K F n) :
    Divisor.IsPrincipal ((n : ℤ) • d.D₂) :=
  d.symm.isPrincipal_smul_left_i

alias isPrincipal_smul_right_i := _root_.AlgebraicCurve.WeilDatum.isPrincipal_smul_right_i
private theorem degree_eq_zero_of_isPrincipal_i [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : Divisor.IsPrincipal D) : Divisor.degree D = 0 := by
  obtain ⟨f, hf, hDv⟩ := hD
  obtain ⟨D', hD'v, hD'deg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  have hDD' : D = D' := Finsupp.ext fun v => by rw [hDv v, hD'v v]
  exact hDD' ▸ hD'deg

private theorem _root_.AlgebraicCurve.WeilDatum.degree_D₁_eq_zero_i [HasPrincipalDivisors K F] (d : WeilDatum K F n) (hn : n ≠ 0) :
    Divisor.degree d.D₁ = 0 := by
  have h := degree_eq_zero_of_isPrincipal_i d.isPrincipal_smul_left_i
  rw [map_zsmul, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn)

alias degree_D₁_eq_zero_i := _root_.AlgebraicCurve.WeilDatum.degree_D₁_eq_zero_i
private theorem _root_.AlgebraicCurve.WeilDatum.degree_D₂_eq_zero_i [HasPrincipalDivisors K F] (d : WeilDatum K F n) (hn : n ≠ 0) :
    Divisor.degree d.D₂ = 0 :=
  d.symm.degree_D₁_eq_zero_i hn

alias degree_D₂_eq_zero_i := _root_.AlgebraicCurve.WeilDatum.degree_D₂_eq_zero_i
section ClassLayer

variable [NeZero n] [HasPrincipalDivisors K F]

private def _root_.AlgebraicCurve.WeilDatum.degZeroLeft_i (d : WeilDatum K F n) : Divisor.degZero (K := K) (F := F) :=
  ⟨d.D₁, Divisor.mem_degZero.mpr (d.degree_D₁_eq_zero_i (NeZero.ne n))⟩

export _root_.AlgebraicCurve.WeilDatum (degZeroLeft_i)

private def _root_.AlgebraicCurve.WeilDatum.degZeroRight_i (d : WeilDatum K F n) : Divisor.degZero (K := K) (F := F) :=
  ⟨d.D₂, Divisor.mem_degZero.mpr (d.degree_D₂_eq_zero_i (NeZero.ne n))⟩

export _root_.AlgebraicCurve.WeilDatum (degZeroRight_i)
theorem coe_degZeroLeft_i (d : WeilDatum K F n) :
    (d.degZeroLeft_i : Divisor K F) = d.D₁ := rfl

theorem coe_degZeroRight_i (d : WeilDatum K F n) :
    (d.degZeroRight_i : Divisor K F) = d.D₂ := rfl

omit [NeZero n] [HasPrincipalDivisors K F] in
theorem mk_mem_torsion_i (D : Divisor.degZero (K := K) (F := F))
    (h : Divisor.IsPrincipal ((n : ℤ) • (D : Divisor K F))) :
    Pic0.mk D ∈ Pic0.torsion K F n := by
  rw [Pic0.mem_torsion]
  have h1 : (n : ℤ) • Pic0.mk D = Pic0.mk ((n : ℤ) • D) := by
    show (n : ℤ) • (QuotientAddGroup.mk D) = QuotientAddGroup.mk ((n : ℤ) • D)
    exact (QuotientAddGroup.mk_zsmul
      ((Divisor.principal (K := K) (F := F)).addSubgroupOf
        (Divisor.degZero (K := K) (F := F))) D (n : ℤ)).symm
  rw [h1]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  have hcoe : (((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) : Divisor K F)
      = (n : ℤ) • (D : Divisor K F) := rfl
  show ((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) ∈
    (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))
  rw [AddSubgroup.mem_addSubgroupOf, hcoe]
  exact Divisor.mem_principal.mpr h

def classLeft_i (d : WeilDatum K F n) : Pic0.torsion K F n :=
  ⟨Pic0.mk d.degZeroLeft_i, mk_mem_torsion_i d.degZeroLeft_i (by
    rw [coe_degZeroLeft_i]; exact d.isPrincipal_smul_left_i)⟩

def classRight_i (d : WeilDatum K F n) : Pic0.torsion K F n :=
  ⟨Pic0.mk d.degZeroRight_i, mk_mem_torsion_i d.degZeroRight_i (by
    rw [coe_degZeroRight_i]; exact d.isPrincipal_smul_right_i)⟩

end ClassLayer

private theorem _root_.AlgebraicCurve.WeilDatum.ord_f₁_eq_zero_of_mem_support_i (d : WeilDatum K F n) {v : Place K F}
    (hv : v ∈ d.D₂.support) : v.ord d.f₁ = 0 := by
  rw [d.ord_f₁ v, (d.disjoint v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero]

alias ord_f₁_eq_zero_of_mem_support_i := _root_.AlgebraicCurve.WeilDatum.ord_f₁_eq_zero_of_mem_support_i
private theorem _root_.AlgebraicCurve.WeilDatum.ord_f₂_eq_zero_of_mem_support_i (d : WeilDatum K F n) {v : Place K F}
    (hv : v ∈ d.D₁.support) : v.ord d.f₂ = 0 := by
  rw [d.ord_f₂ v, (d.disjoint v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero]

alias ord_f₂_eq_zero_of_mem_support_i := _root_.AlgebraicCurve.WeilDatum.ord_f₂_eq_zero_of_mem_support_i
private theorem _root_.AlgebraicCurve.WeilDatum.rational_of_mem_support_left_i (d : WeilDatum K F n) {v : Place K F}
    (hv : v ∈ d.D₁.support) : v.IsRational :=
  d.rational v (Or.inl (Finsupp.mem_support_iff.mp hv))

alias rational_of_mem_support_left_i := _root_.AlgebraicCurve.WeilDatum.rational_of_mem_support_left_i
private theorem _root_.AlgebraicCurve.WeilDatum.rational_of_mem_support_right_i (d : WeilDatum K F n) {v : Place K F}
    (hv : v ∈ d.D₂.support) : v.IsRational :=
  d.rational v (Or.inr (Finsupp.mem_support_iff.mp hv))

alias rational_of_mem_support_right_i := _root_.AlgebraicCurve.WeilDatum.rational_of_mem_support_right_i
theorem evalAt_f₁_ne_zero_i (d : WeilDatum K F n) {v : Place K F}
    (hv : v ∈ d.D₂.support) : v.evalAt d.f₁ ≠ 0 :=
  v.evalAt_ne_zero (d.rational_of_mem_support_right_i hv) d.f₁_ne_zero
    (d.ord_f₁_eq_zero_of_mem_support_i hv)

private theorem _root_.AlgebraicCurve.WeilDatum.evalAt_f₂_ne_zero_i (d : WeilDatum K F n) {v : Place K F}
    (hv : v ∈ d.D₁.support) : v.evalAt d.f₂ ≠ 0 :=
  v.evalAt_ne_zero (d.rational_of_mem_support_left_i hv) d.f₂_ne_zero
    (d.ord_f₂_eq_zero_of_mem_support_i hv)

alias evalAt_f₂_ne_zero_i := _root_.AlgebraicCurve.WeilDatum.evalAt_f₂_ne_zero_i

theorem pairing_eq_of_addPrincipalLeft_i (hrec : WeilReciprocity K F)
    (d d' : WeilDatum K F n) {E : Divisor K F} {h : F} (hh : h ≠ 0)
    (hE : ∀ v : Place K F, E v = v.ord h)
    (hD₁ : d'.D₁ = d.D₁ + E) (hD₂ : d'.D₂ = d.D₂)
    (hf₁ : d'.f₁ = d.f₁ * h ^ (n : ℤ)) (hf₂ : d'.f₂ = d.f₂) :
    d'.pairing = d.pairing := by
  classical
  have hE0 : ∀ v : Place K F, d.D₂ v ≠ 0 → E v = 0 := by
    intro v hv
    have h1 : d.D₁ v = 0 := (d.disjoint v).resolve_right hv
    have h2 : d'.D₁ v = 0 := (d'.disjoint v).resolve_right (by rw [hD₂]; exact hv)
    have h3 : d'.D₁ v = d.D₁ v + E v := by rw [hD₁]; rfl
    rw [h1, h2, zero_add] at h3
    exact h3.symm
  have hordh : ∀ v ∈ d.D₂.support, v.ord h = 0 := by
    intro v hv
    rw [← hE v]
    exact hE0 v (Finsupp.mem_support_iff.mp hv)
  have hratD₂ : ∀ v ∈ d.D₂.support, Place.IsRational v :=
    fun v hv => d.rational_of_mem_support_right_i hv
  have hratE : ∀ v ∈ E.support, Place.IsRational v := by
    intro v hv
    have hEv : E v ≠ 0 := Finsupp.mem_support_iff.mp hv
    by_cases hD₁v : d.D₁ v = 0
    · refine d'.rational v (Or.inl ?_)
      rw [hD₁]
      show d.D₁ v + E v ≠ 0
      rw [hD₁v, zero_add]
      exact hEv
    · exact d.rational v (Or.inl hD₁v)
  have hordf₂E : ∀ v ∈ E.support, v.ord d.f₂ = 0 := by
    intro v hv
    have hEv : E v ≠ 0 := Finsupp.mem_support_iff.mp hv
    have hD₂v : d.D₂ v = 0 := by
      by_contra hne
      exact hEv (hE0 v hne)
    rw [d.ord_f₂ v, hD₂v, mul_zero]
  have hevalf₂E : ∀ v ∈ E.support, v.evalAt d.f₂ ≠ 0 := fun v hv =>
    v.evalAt_ne_zero (hratE v hv) d.f₂_ne_zero (hordf₂E v hv)
  have hnum : Divisor.evalFun d'.f₁ d'.D₂
      = Divisor.evalFun d.f₁ d.D₂ * Divisor.evalFun h d.D₂ ^ (n : ℤ) := by
    rw [hf₁, hD₂,
      Divisor.evalFun_mul hratD₂
        (fun v hv => v.mem_of_ord_nonneg d.f₁_ne_zero
          (d.ord_f₁_eq_zero_of_mem_support_i hv).ge)
        (fun v hv => v.mem_of_ord_nonneg (zpow_ne_zero _ hh)
          (by rw [Place.ord_zpow, hordh v hv, mul_zero])),
      Divisor.evalFun_zpow_left hh (n : ℤ) hratD₂ hordh]
  have hrecip : Divisor.evalFun h d.D₂ ^ (n : ℤ) = Divisor.evalFun d.f₂ E := by
    rw [← Divisor.evalFun_zsmul]
    refine (hrec d.f₂ h ((n : ℤ) • d.D₂) E d.f₂_ne_zero hh
      (fun v => ?_) (fun v => (hE v).symm ▸ rfl) (fun v => ?_) (fun v hv => ?_) hratE).symm
    · rw [Finsupp.smul_apply, smul_eq_mul, d.ord_f₂ v]
    · by_cases hD₂v : d.D₂ v = 0
      · exact Or.inl (by rw [d.ord_f₂ v, hD₂v, mul_zero])
      · exact Or.inr (by rw [← hE v]; exact hE0 v hD₂v)
    · exact hratD₂ v (support_zsmul_subset_i _ _ hv)
  have hden : Divisor.evalFun d'.f₂ d'.D₁
      = Divisor.evalFun d.f₂ d.D₁ * Divisor.evalFun d.f₂ E := by
    rw [hf₂, hD₁]
    exact Divisor.evalFun_add d.f₂ (fun v hv => d.evalAt_f₂_ne_zero_i hv) hevalf₂E
  have hEne : Divisor.evalFun d.f₂ E ≠ 0 := Divisor.evalFun_ne_zero hevalf₂E
  show Divisor.evalFun d'.f₁ d'.D₂ / Divisor.evalFun d'.f₂ d'.D₁ = d.pairing
  rw [hnum, hrecip, hden]
  rw [show d.pairing = Divisor.evalFun d.f₁ d.D₂ / Divisor.evalFun d.f₂ d.D₁ from rfl]
  rw [mul_div_mul_right _ _ hEne]

theorem pairing_eq_of_isPrincipal_sub_left_i [NeZero n] [HasPrincipalDivisors K F]
    (hrec : WeilReciprocity K F)
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c)
    (d d' : WeilDatum K F n) (hD₂ : d'.D₂ = d.D₂) (hf₂ : d'.f₂ = d.f₂)
    (hprin : Divisor.IsPrincipal (d'.D₁ - d.D₁)) :
    d'.pairing = d.pairing := by
  classical
  obtain ⟨h, hh0, hhord⟩ := hprin
  set w : F := d.f₁ * h ^ (n : ℤ) with hw
  have hw0 : w ≠ 0 := mul_ne_zero d.f₁_ne_zero (zpow_ne_zero _ hh0)
  have hordw : ∀ v : Place K F, v.ord w = n * d'.D₁ v := by
    intro v
    rw [hw, v.ord_mul d.f₁_ne_zero (zpow_ne_zero _ hh0), Place.ord_zpow, d.ord_f₁ v,
      ← hhord v, Finsupp.sub_apply]
    ring
  set d'' : WeilDatum K F n :=
    ⟨d'.D₁, d.D₂, w, d.f₂, hw0, d.f₂_ne_zero, hordw, d.ord_f₂,
      fun v => by rw [← hD₂]; exact d'.disjoint v,
      fun v hv => d'.rational v (by rw [hD₂]; exact hv)⟩ with hd''
  have hengine : d''.pairing = d.pairing := by
    refine pairing_eq_of_addPrincipalLeft_i hrec d d'' hh0 hhord ?_ rfl rfl rfl
    show d'.D₁ = d.D₁ + (d'.D₁ - d.D₁)
    abel
  have hordu : ∀ v : Place K F, v.ord (d'.f₁ * w⁻¹) = 0 := by
    intro v
    rw [v.ord_mul d'.f₁_ne_zero (inv_ne_zero hw0), Place.ord_inv, d'.ord_f₁ v, hordw v]
    ring
  obtain ⟨c, hc⟩ := hconst (d'.f₁ * w⁻¹) (mul_ne_zero d'.f₁_ne_zero (inv_ne_zero hw0)) hordu
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (mul_ne_zero d'.f₁_ne_zero (inv_ne_zero hw0)) (by rw [hc, map_zero])
  have hf₁' : d'.f₁ = algebraMap K F c * w := by
    have h1 : d'.f₁ * w⁻¹ * w = algebraMap K F c * w := by rw [hc]
    rwa [mul_assoc, inv_mul_cancel₀ hw0, mul_one] at h1
  have hratD₂ : ∀ v ∈ d.D₂.support, Place.IsRational v :=
    fun v hv => d.rational_of_mem_support_right_i hv
  have hordwD₂ : ∀ v ∈ d.D₂.support, v.ord w = 0 := by
    intro v hv
    rw [hordw v]
    have hzero : d'.D₁ v = 0 := (d'.disjoint v).resolve_right (by
      rw [hD₂]
      exact Finsupp.mem_support_iff.mp hv)
    rw [hzero, mul_zero]
  have hnum : Divisor.evalFun d'.f₁ d.D₂ = Divisor.evalFun w d.D₂ := by
    rw [hf₁', Divisor.evalFun_mul hratD₂
      (fun v _ => v.algebraMap_mem' c)
      (fun v hv => v.mem_of_ord_nonneg hw0 (hordwD₂ v hv).ge),
      evalFun_algebraMap_of_degree_eq_zero_i hc0 (d.degree_D₂_eq_zero_i (NeZero.ne n))
        hratD₂, one_mul]
  have hpair' : d'.pairing = d''.pairing := by
    show Divisor.evalFun d'.f₁ d'.D₂ / Divisor.evalFun d'.f₂ d'.D₁
      = Divisor.evalFun w d.D₂ / Divisor.evalFun d.f₂ d'.D₁
    rw [hD₂, hf₂, hnum]
  rw [hpair', hengine]

theorem pairing_eq_of_isPrincipal_sub_right_i [NeZero n] [HasPrincipalDivisors K F]
    (hrec : WeilReciprocity K F)
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c)
    (d d' : WeilDatum K F n) (hD₁ : d'.D₁ = d.D₁) (hf₁ : d'.f₁ = d.f₁)
    (hprin : Divisor.IsPrincipal (d'.D₂ - d.D₂)) :
    d'.pairing = d.pairing := by
  have hsymm : d'.symm.pairing = d.symm.pairing := by
    refine pairing_eq_of_isPrincipal_sub_left_i hrec hconst d.symm d'.symm ?_ ?_ ?_
    · show d'.D₁ = d.D₁
      exact hD₁
    · show d'.f₁ = d.f₁
      exact hf₁
    · show Divisor.IsPrincipal (d'.D₂ - d.D₂)
      exact hprin
  rw [WeilDatum.symm_pairing, WeilDatum.symm_pairing] at hsymm
  exact inv_inj.mp hsymm

end WeilDatum

end AlgebraicCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub.AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]
    (hrec : WeilReciprocity K F)
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c)
    (hmove : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
      ∃ D : Divisor.degZero (K := K) (F := F),
        Pic0.mk D = (x : Pic0 K F) ∧
        (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
        (∀ v ∈ (D : Divisor K F).support, v ∉ S))
    (d d' : WeilDatum K F n)
    (hL : Divisor.IsPrincipal (d'.D₁ - d.D₁)) (hR : Divisor.IsPrincipal (d'.D₂ - d.D₂)) :
    d'.pairing = d.pairing := by
  classical
  obtain ⟨A₁, hA₁mk, hA₁rat, hA₁avoid⟩ := hmove (WeilDatum.classLeft_i d) d.D₂.support
  obtain ⟨A₂, hA₂mk, hA₂rat, hA₂avoid⟩ :=
    hmove (WeilDatum.classRight_i d) ((A₁ : Divisor K F).support ∪ d'.D₁.support)
  obtain ⟨a₁, ha₁0, ha₁⟩ :=
    Pic0.torsion.exists_forall_ord_eq_mul (WeilDatum.classLeft_i d) A₁ hA₁mk
  obtain ⟨a₂, ha₂0, ha₂⟩ :=
    Pic0.torsion.exists_forall_ord_eq_mul (WeilDatum.classRight_i d) A₂ hA₂mk
  set e₁ : WeilDatum K F n :=
    ⟨(A₁ : Divisor K F), d.D₂, a₁, d.f₂, ha₁0, d.f₂_ne_zero, ha₁, d.ord_f₂,
      fun v => by
        by_cases hv : (A₁ : Divisor K F) v = 0
        · exact Or.inl hv
        · refine Or.inr ?_
          by_contra hv2
          exact hA₁avoid v (Finsupp.mem_support_iff.mpr hv) (Finsupp.mem_support_iff.mpr hv2),
      fun v hv => by
        rcases hv with h1 | h2
        · exact hA₁rat v (Finsupp.mem_support_iff.mpr h1)
        · exact d.rational v (Or.inr h2)⟩ with he₁
  set e₂ : WeilDatum K F n :=
    ⟨(A₁ : Divisor K F), (A₂ : Divisor K F), a₁, a₂, ha₁0, ha₂0, ha₁, ha₂,
      fun v => by
        by_cases hv : (A₂ : Divisor K F) v = 0
        · exact Or.inr hv
        · refine Or.inl ?_
          by_contra hv2
          exact hA₂avoid v (Finsupp.mem_support_iff.mpr hv)
            (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hv2)),
      fun v hv => by
        rcases hv with h1 | h2
        · exact hA₁rat v (Finsupp.mem_support_iff.mpr h1)
        · exact hA₂rat v (Finsupp.mem_support_iff.mpr h2)⟩ with he₂
  set e₃ : WeilDatum K F n :=
    ⟨d'.D₁, (A₂ : Divisor K F), d'.f₁, a₂, d'.f₁_ne_zero, ha₂0, d'.ord_f₁, ha₂,
      fun v => by
        by_cases hv : (A₂ : Divisor K F) v = 0
        · exact Or.inr hv
        · refine Or.inl ?_
          by_contra hv2
          exact hA₂avoid v (Finsupp.mem_support_iff.mpr hv)
            (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hv2)),
      fun v hv => by
        rcases hv with h1 | h2
        · exact d'.rational v (Or.inl h1)
        · exact hA₂rat v (Finsupp.mem_support_iff.mpr h2)⟩ with he₃

  have hA₁cl : Pic0.mk A₁ = Pic0.mk (WeilDatum.degZeroLeft_i d) := hA₁mk
  have hA₂cl : Pic0.mk A₂ = Pic0.mk (WeilDatum.degZeroRight_i d) := hA₂mk
  have iL1 : Divisor.IsPrincipal ((A₁ : Divisor K F) - d.D₁) :=
    AlgebraicCurve.isPrincipal_sub_of_mk_eq_i hA₁cl
  have iR2 : Divisor.IsPrincipal ((A₂ : Divisor K F) - d.D₂) :=
    AlgebraicCurve.isPrincipal_sub_of_mk_eq_i hA₂cl
  have iL1' : Divisor.IsPrincipal (d.D₁ - (A₁ : Divisor K F)) := by
    have hneg := AlgebraicCurve.isPrincipal_neg_i iL1
    rwa [neg_sub] at hneg
  have iR2' : Divisor.IsPrincipal (d.D₂ - (A₂ : Divisor K F)) := by
    have hneg := AlgebraicCurve.isPrincipal_neg_i iR2
    rwa [neg_sub] at hneg
  have iL3 : Divisor.IsPrincipal (d'.D₁ - (A₁ : Divisor K F)) := by
    have hadd := AlgebraicCurve.isPrincipal_add_i hL iL1'
    rwa [sub_add_sub_cancel] at hadd
  have iR4 : Divisor.IsPrincipal (d'.D₂ - (A₂ : Divisor K F)) := by
    have hadd := AlgebraicCurve.isPrincipal_add_i hR iR2'
    rwa [sub_add_sub_cancel] at hadd

  have h₁ : e₁.pairing = d.pairing :=
    WeilDatum.pairing_eq_of_isPrincipal_sub_left_i hrec hconst d e₁ rfl rfl iL1
  have h₂ : e₂.pairing = e₁.pairing :=
    WeilDatum.pairing_eq_of_isPrincipal_sub_right_i hrec hconst e₁ e₂ rfl rfl iR2
  have h₃ : e₃.pairing = e₂.pairing :=
    WeilDatum.pairing_eq_of_isPrincipal_sub_left_i hrec hconst e₂ e₃ rfl rfl iL3
  have h₄ : d'.pairing = e₃.pairing :=
    WeilDatum.pairing_eq_of_isPrincipal_sub_right_i hrec hconst e₃ d' rfl rfl iR4
  rw [h₄, h₃, h₂, h₁]

end
