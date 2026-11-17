/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd (git blob 5f5c89a098e4a9ccbd64989528b119ae76e51665, sha256 3247db6b4cffc553bd57628232076d3c790c915e352d4631d78243ebe86532b3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_isPrimitiveForm_inv_of_qCoeff_eq_conj
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd.PrimitiveCosetSum
end P2MW.S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd.PrimitiveCosetSum

namespace P2MW.S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd

set_option autoImplicit false

open CongruenceSubgroup ModularFormClass UpperHalfPlane ModularForm
open scoped MatrixGroups ComplexConjugate ModularForm

noncomputable section

namespace PrimitiveCosetSum



section QCoeff

variable {L : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem periodic (f : CuspForm (((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) : Function.Periodic (⇑f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods L)

theorem bdd (f : CuspForm (((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) : IsBoundedAtImInfty (⇑f) := by
  haveI : Fact (IsCusp OnePoint.infty (((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))) :=
    ⟨(((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods L)⟩
  exact ModularFormClass.bdd_at_infty f

theorem analytic (f : CuspForm (((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 :=
  analyticAt_cuspFunction_zero one_pos (periodic f) f.holo' (bdd f)

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_smul (c : ℂ) (f : CuspForm (((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  rw [qCoeff, qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul (analytic f), map_smul,
    smul_eq_mul]

end QCoeff

def frickeGL (M : ℕ) [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp] theorem val_frickeGL (M : ℕ) [NeZero M] :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL_pos (M : ℕ) [NeZero M] : 0 < ((frickeGL M).det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]
  have : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  linarith

theorem coe_frickeGL_smul (M : ℕ) [NeZero M] (τ : ℍ) :
    (↑(frickeGL M • τ) : ℂ) = -1 / ((M : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_frickeGL_pos M)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, val_frickeGL, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_natCast, add_zero]

theorem frickeGL_smul_mul (M : ℕ) [NeZero M] (τ : ℍ) :
    ((frickeGL M • τ : ℍ) : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 := by
  rw [coe_frickeGL_smul]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  field_simp

variable {M : ℕ} [NeZero M] {k : ℤ}

omit [NeZero M] in
theorem ne_zero_of_isPrimitiveForm {ε : DirichletCharacter ℂ M} {g : CuspForm (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k}
    (hg : CuspForm.IsPrimitiveForm ε g) : g ≠ 0 := by
  intro h0
  have h1 := hg.isEigenformWith.qCoeff_one
  rw [h0, CuspForm.coe_zero, qCoeff_zero_fun] at h1
  exact zero_ne_one h1

theorem main (ε : DirichletCharacter ℂ M) (g : CuspForm (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k)
    (hg : CuspForm.IsPrimitiveForm ε g) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (τ : ℍ) :
    ∑ j ∈ Finset.range q,
        ((⇑g : ℍ → ℂ) ∣[k]
          (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * (M / q : ℕ)) * ModularGroup.S⁻¹ :
            SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * conj (qCoeff g q) * g (heckeMatrix q 0 • τ) := by
  have hg0 : g ≠ 0 := ne_zero_of_isPrimitiveForm hg
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M

  obtain ⟨g', -, hg'⟩ := CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj M k g
  obtain ⟨c, hc0, hc⟩ :=
    CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm M k ε g hg g' hg'
  have hg'prim : CuspForm.IsPrimitiveForm ε⁻¹ g' :=
    CuspForm.isPrimitiveForm_inv_of_qCoeff_eq_conj M k ε g hg g' hg'
  have hgg' : ∀ n : ℕ, qCoeff g n = conj (qCoeff g' n) := fun n => by
    rw [hg' n, Complex.conj_conj]
  obtain ⟨c', -, hc'⟩ :=
    CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm M k ε⁻¹ g' hg'prim g hgg'

  have hcc' : c * c' = (-(M : ℂ)) ^ k := by
    obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : ℍ, g τ₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hg0 (DFunLike.ext g 0 fun τ => by rw [h τ, CuspForm.zero_apply])
    set W : ℍ := frickeGL M • τ₀ with hW
    have hrelW : (W : ℂ) * ((M : ℂ) * (τ₀ : ℂ)) = -1 := frickeGL_smul_mul M τ₀
    have hrel0 : (τ₀ : ℂ) * ((M : ℂ) * (W : ℂ)) = -1 := by linear_combination hrelW
    have h1 : g τ₀ = c * (W : ℂ) ^ k * g' W := hc W τ₀ hrel0
    have h2 : g' W = c' * (τ₀ : ℂ) ^ k * g τ₀ := hc' τ₀ W hrelW
    have hWτ : (W : ℂ) * (τ₀ : ℂ) = -1 / (M : ℂ) := by
      have hτ₀ne : (τ₀ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ₀
      field_simp
      linear_combination hrelW
    have h3 : c * c' * ((W : ℂ) * (τ₀ : ℂ)) ^ k * g τ₀ = g τ₀ := by
      rw [mul_zpow]
      calc c * c' * ((W : ℂ) ^ k * (τ₀ : ℂ) ^ k) * g τ₀
          = c * (W : ℂ) ^ k * (c' * (τ₀ : ℂ) ^ k * g τ₀) := by ring
        _ = g τ₀ := by rw [← h2, ← h1]
    have h4 : c * c' * ((W : ℂ) * (τ₀ : ℂ)) ^ k = 1 := by
      have := mul_right_cancel₀ hτ₀ (h3.trans (one_mul (g τ₀)).symm)
      exact this
    rw [hWτ] at h4
    have hMk : (-(M : ℂ)) ^ k ≠ 0 := zpow_ne_zero k (neg_ne_zero.mpr hMC)
    have h5 : (-1 / (M : ℂ)) ^ k * (-(M : ℂ)) ^ k = 1 := by
      rw [← mul_zpow, show (-1 / (M : ℂ)) * (-(M : ℂ)) = 1 by field_simp, one_zpow]
    calc c * c' = c * c' * ((-1 / (M : ℂ)) ^ k * (-(M : ℂ)) ^ k) := by rw [h5, mul_one]
      _ = (c * c' * (-1 / (M : ℂ)) ^ k) * (-(M : ℂ)) ^ k := by ring
      _ = (-(M : ℂ)) ^ k := by rw [h4, one_mul]

  set H : CuspForm (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k := c • g' with hHdef
  have hH : ∀ τ : ℍ, H τ = c * g' τ := fun τ => by
    rw [hHdef, CuspForm.IsGLPos.smul_apply, smul_eq_mul]
  obtain ⟨U, hUcoe, hUcoef, -⟩ := CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd k hqM H
  have heig := hg.isEigenformWith
  have hUeq : U = conj (qCoeff g q) • H := by
    refine ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods M) fun n => ?_
    rw [hUcoef n, qCoeff_smul, hHdef, qCoeff_smul, qCoeff_smul, hg', hg',
      heig.hecke_of_dvd hq hqM n, map_mul]
    ring
  have hUfun : heckeU k q (⇑H) = fun τ => conj (qCoeff g q) * (c * g' τ) := by
    rw [← hUcoe, hUeq]
    funext τ
    rw [CuspForm.IsGLPos.smul_apply, smul_eq_mul, hH]

  have key := UpperHalfPlane.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU M k
    hq.ne_zero hqM (⇑g) (⇑H) (fun τ => conj (qCoeff g q) * (c * c') * g τ)
    (fun τ τ' hττ' => by rw [hH, hc τ τ' hττ']; ring)
    (fun τ τ' hττ' => by
      rw [hUfun]
      simp only
      rw [hc' τ τ' hττ']; ring)
    τ
  rw [key, hcc']
  have hMk : (-(M : ℂ)) ^ k ≠ 0 := zpow_ne_zero k (neg_ne_zero.mpr hMC)
  rw [zpow_neg]
  field_simp

end PrimitiveCosetSum
open scoped _root_.P2MW.S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd.PrimitiveCosetSum

end
open scoped _root_.P2MW.S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd.PrimitiveCosetSum

open scoped MatrixGroups ModularForm in
theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M)
    (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg : CuspForm.IsPrimitiveForm ε g)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (τ : UpperHalfPlane) :
    ∑ j ∈ Finset.range q,
        ((⇑g : UpperHalfPlane → ℂ) ∣[k]
          (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * (M / q : ℕ)) * ModularGroup.S⁻¹ :
            SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * starRingEnd ℂ (ModularFormClass.qCoeff g q) *
          g (ModularForm.heckeMatrix q 0 • τ) :=
  PrimitiveCosetSum.main ε g hg hq hqM τ
