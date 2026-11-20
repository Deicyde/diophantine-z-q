/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_IsPrimitiveForm_qCoeff_eq_zero_of_dvd_div (git blob 7b46b305bc2cf8fa42e17436bdac45baee1a8de6, sha256 a685b1214285008b514c4053bd6d72d3e1b2759c6f06eab844e4479b550f47de).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspForm_IsPrimitiveForm_qCoeff_eq_zero_of_dvd_div

set_option autoImplicit false

open CongruenceSubgroup ModularFormClass

namespace LiThreeVanishing

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : UpperHalfPlane → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

theorem changeLevel_apply_natCast {M M' : ℕ} [NeZero M] (h : M' ∣ M)
    (χ : DirichletCharacter ℂ M') {p : ℕ} (hp : Nat.Coprime p M) :
    DirichletCharacter.changeLevel h χ (p : ZMod M) = χ (p : ZMod M') := by
  have hu : IsUnit (p : ZMod M) := (ZMod.isUnit_iff_coprime p M).mpr hp
  rw [← hu.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd χ h, hu.unit_spec,
    ZMod.cast_natCast h]

theorem main (M : ℕ) [NeZero M] (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hqq : q ∣ M / q)
    (ε' : DirichletCharacter ℂ (M / q)) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM) ε') g) :
    qCoeff g q = 0 := by
  have hM0 : M ≠ 0 := NeZero.ne M
  obtain ⟨h, -, hcoef, hneb⟩ :=
    CuspForm.exists_gamma1_div_coe_eq_heckeU_of_dvd_div k hqM hqq ε' g hg.isEigenformWith.hasNebentypus

  have ha : qCoeff g q = qCoeff h 1 := by rw [hcoef 1, mul_one]
  rw [ha]
  by_contra hne
  have hh0 : h ≠ 0 := by
    intro h0; apply hne; rw [h0, CuspForm.coe_zero, qCoeff_zero_fun]

  have hocc : CuspForm.EigenpacketOccursAt k (fun n => qCoeff g n)
      (fun n => DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM) ε' (n : ZMod M)) (M / q) := by
    refine ⟨ε', h, hh0, hneb, M.primeFactors, fun p hp hpS => ?_⟩
    have hpM : ¬ p ∣ M := fun hd => hpS (Nat.mem_primeFactors.mpr ⟨hp, hd, hM0⟩)
    have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM
    refine ⟨(changeLevel_apply_natCast _ ε' hcop).symm, fun n => ?_⟩
    have hpq : ¬ p ∣ q := fun hd => hpM (hd.trans hqM)
    have hrel := hg.isEigenformWith.hecke_of_not_dvd hp hpM (q * n)
    rw [changeLevel_apply_natCast _ ε' hcop] at hrel
    rw [hcoef, hcoef, hcoef, mul_left_comm]
    have hiff : (p ∣ q * n ↔ p ∣ n) :=
      ⟨fun hd => (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq) hd),
        fun hd => hd.mul_left q⟩
    by_cases hpn : p ∣ n
    · rw [if_pos hpn]
      rw [if_pos (hiff.mpr hpn), Nat.mul_div_assoc q hpn] at hrel
      exact hrel
    · rw [if_neg hpn]
      rw [if_neg (fun hd => hpn (hiff.mp hd))] at hrel
      exact hrel
  have hlt : M / q < M := Nat.div_lt_self (Nat.pos_of_ne_zero hM0) hq.one_lt
  exact hg.not_eigenpacketOccursAt (Nat.div_dvd_of_dvd hqM) hlt.ne hocc

end LiThreeVanishing

theorem solution (M : ℕ) [NeZero M] (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hqq : q ∣ M / q)
    (ε' : DirichletCharacter ℂ (M / q)) (g : CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm
      (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM) ε') g) :
    ModularFormClass.qCoeff g q = 0 :=
  LiThreeVanishing.main M k hq hqM hqq ε' g hg
