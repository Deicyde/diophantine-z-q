/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CohCarrier_exists_eichlerShimura_H1_gammaH (git blob 00529bfe82ec045d4dbc70c2534f926391f8e4d2, sha256 e7866c3ef83777d26bcb86e38661c959f78aee24f6351bbcc63d4cd332301fd3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodHomPair
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_CharInvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_periodMapOf_mem_parabolicHoms
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CohCarrier_charInvolution_comp_opFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_stableT
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_stableU
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_stableD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace CohCarrier
end CohCarrier

namespace P2MW.S_CohCarrier_exists_eichlerShimura_H1_gammaH

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularCurve ModularCurve.Period UpperHalfPlane
open scoped MatrixGroups ModularForm ComplexConjugate

namespace CohCarrier
export _root_.CohCarrier (Gen diamondL diamondL_eq_diamondRaw Gen.T Gen.dia Gen.U GammaH H1 heckeT jConjSL_mem_GammaH jConjGammaH coe_jConjGammaH jConjGammaH_jConjGammaH charInvolution charInvolution_charInvolution charInvolution_comp_opFamily)
namespace ESGammaH
open _root_.CohCarrier

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

section Reflection

private theorem jConjSL_entry_00 (γ : SL(2, ℤ)) : (jConjSL γ) 0 0 = γ 0 0 := by
  show jConjMat ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = _
  rw [jConjMat_apply_zero_zero]

private theorem jConjSL_entry_01 (γ : SL(2, ℤ)) : (jConjSL γ) 0 1 = -(γ 0 1) := by
  show jConjMat ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = _
  rw [jConjMat_apply_zero_one]

private theorem jConjSL_entry_10 (γ : SL(2, ℤ)) : (jConjSL γ) 1 0 = -(γ 1 0) := by
  show jConjMat ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = _
  rw [jConjMat_apply_one_zero]

private theorem jConjSL_entry_11 (γ : SL(2, ℤ)) : (jConjSL γ) 1 1 = γ 1 1 := by
  show jConjMat ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = _
  rw [jConjMat_apply_one_one]

private theorem J_smul_sl_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.J • (γ • τ) = jConjSL γ • (UpperHalfPlane.J • τ) := by
  ext1
  rw [coe_J_smul, UpperHalfPlane.coe_specialLinearGroup_apply,
    UpperHalfPlane.coe_specialLinearGroup_apply, coe_J_smul,
    jConjSL_entry_00, jConjSL_entry_01, jConjSL_entry_10, jConjSL_entry_11,
    map_neg, map_neg, Complex.ofReal_neg, Complex.ofReal_neg, map_div₀, map_add, map_add,
    map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal,
    Complex.conj_ofReal]
  ring

private theorem J_smul_I : UpperHalfPlane.J • UpperHalfPlane.I = UpperHalfPlane.I := by
  ext1
  rw [coe_J_smul, coe_I, Complex.conj_I, neg_neg]

end Reflection

section Twins

omit [NeZero M] in

private theorem periodOf_jConj (f fρ : CuspForm (CohCarrier.GammaH M H) 2)
    (hρ : ∀ τ : ℍ, fρ τ = conj (f (UpperHalfPlane.J • τ))) (γ : ↥(CohCarrier.GammaH M H)) :
    periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) f =
      -conj (periodOf (CohCarrier.GammaH M H) γ fρ) := by
  have h := periodAlongOf_eq_neg_conj_periodAlongOf_J_smul (CohCarrier.GammaH M H) f fρ hρ
    UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I)
  rw [J_smul_sl_smul, J_smul_I] at h
  show periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I
      (((jConjGammaH M H γ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) • UpperHalfPlane.I) f =
    -conj (periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I) fρ)
  rw [coe_jConjGammaH, h, map_neg, neg_neg, Complex.conj_conj]

private theorem eq_zero_of_periodOf_eq_conj (h h' : CuspForm (CohCarrier.GammaH M H) 2)
    (hc : ∀ γ : ↥(CohCarrier.GammaH M H),
      periodOf (CohCarrier.GammaH M H) γ h = conj (periodOf (CohCarrier.GammaH M H) γ h')) :
    h = 0 := by

  have hsum : Complex.I • (h + h') = 0 := by
    refine eq_zero_of_forall_re_periodOf_eq_zero (CohCarrier.GammaH M H) _ fun γ => ?_
    rw [map_smul, map_add, smul_eq_mul, hc γ]
    set p : ℂ := periodOf (CohCarrier.GammaH M H) γ h' with hp
    have e : conj p + p = ((2 * p.re : ℝ) : ℂ) := by rw [add_comm, Complex.add_conj]
    rw [e, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hh' : h' = -h := by
    have h0 : h + h' = 0 := (smul_eq_zero.mp hsum).resolve_left Complex.I_ne_zero
    exact eq_neg_of_add_eq_zero_right h0
  subst hh'
  refine eq_zero_of_forall_re_periodOf_eq_zero (CohCarrier.GammaH M H) h fun γ => ?_
  have h1 := hc γ
  rw [map_neg, map_neg] at h1
  have hre := congrArg Complex.re h1
  rw [Complex.neg_re, Complex.conj_re] at hre
  linarith

private theorem twin_plus (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : ∀ γ : ↥(CohCarrier.GammaH M H),
      periodOf (CohCarrier.GammaH M H) γ f +
        periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) f = 0) : f = 0 := by
  obtain ⟨fρ, hρ⟩ := CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem
    (CohCarrier.GammaH M H) (fun γ hγ => jConjSL_mem_GammaH M H hγ) 2 f
  refine eq_zero_of_periodOf_eq_conj M H f fρ fun γ => ?_
  have h1 := hf γ
  rw [periodOf_jConj M H f fρ hρ γ] at h1
  linear_combination h1

private theorem twin_minus (g : CuspForm (CohCarrier.GammaH M H) 2)
    (hg : ∀ γ : ↥(CohCarrier.GammaH M H),
      periodOf (CohCarrier.GammaH M H) γ g -
        periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) g = 0) : g = 0 := by
  obtain ⟨gρ, hρ⟩ := CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem
    (CohCarrier.GammaH M H) (fun γ hγ => jConjSL_mem_GammaH M H hγ) 2 g
  refine eq_zero_of_periodOf_eq_conj M H g (-gρ) fun γ => ?_
  have h1 := hg γ
  rw [periodOf_jConj M H g gρ hρ γ] at h1
  rw [map_neg, map_neg]
  linear_combination h1

end Twins

section Maps

private def perLin : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CohCarrier.H1 M H ℂ where
  toFun f := periodMapOf (CohCarrier.GammaH M H) f
  map_add' f g := by
    refine AddMonoidHom.ext fun x => ?_
    have e : x = Additive.ofMul (Additive.toMul x) := rfl
    rw [AddMonoidHom.add_apply, e, periodMapOf_apply_eq_periodOf, periodMapOf_apply_eq_periodOf,
      periodMapOf_apply_eq_periodOf, map_add]
  map_smul' c f := by
    refine AddMonoidHom.ext fun x => ?_
    have e : x = Additive.ofMul (Additive.toMul x) := rfl
    rw [RingHom.id_apply, AddMonoidHom.smul_apply, e, periodMapOf_apply_eq_periodOf,
      periodMapOf_apply_eq_periodOf, map_smul]

private theorem perLin_apply (f : CuspForm (CohCarrier.GammaH M H) 2) :
    perLin M H f = periodMapOf (CohCarrier.GammaH M H) f := rfl

private theorem perLin_apply_ofMul (f : CuspForm (CohCarrier.GammaH M H) 2) (γ : ↥(CohCarrier.GammaH M H)) :
    perLin M H f (Additive.ofMul γ) = periodOf (CohCarrier.GammaH M H) γ f :=
  periodMapOf_apply_eq_periodOf _ f γ

private def ι : CohCarrier.H1 M H ℂ →ₗ[ℂ] CohCarrier.H1 M H ℂ := CohCarrier.charInvolution M H ℂ ℂ

omit [NeZero M] in
private theorem ι_apply_ofMul (φ : CohCarrier.H1 M H ℂ) (γ : ↥(CohCarrier.GammaH M H)) :
    ι M H φ (Additive.ofMul γ) = φ (Additive.ofMul (jConjGammaH M H γ)) := rfl

omit [NeZero M] in
private theorem ι_ι (φ : CohCarrier.H1 M H ℂ) : ι M H (ι M H φ) = φ :=
  charInvolution_charInvolution M H ℂ ℂ φ

omit [NeZero M] in

private theorem ι_mem_parabolicHoms {φ : CohCarrier.H1 M H ℂ}
    (hφ : φ ∈ parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) :
    ι M H φ ∈ parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ := by
  rw [mem_parabolicHoms_iff] at hφ ⊢
  intro γ hγ
  rw [ι_apply_ofMul]
  refine hφ (jConjGammaH M H γ) ?_
  have htr : (((jConjGammaH M H γ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
    rw [coe_jConjGammaH, jConjSL_coe, jConjMat_trace]
  rw [htr]
  exact hγ

private def ES : (CuspForm (CohCarrier.GammaH M H) 2 × CuspForm (CohCarrier.GammaH M H) 2) →ₗ[ℂ]
    CohCarrier.H1 M H ℂ :=
  LinearMap.coprod ((LinearMap.id + ι M H) ∘ₗ perLin M H) ((LinearMap.id - ι M H) ∘ₗ perLin M H)

private theorem ES_apply (f g : CuspForm (CohCarrier.GammaH M H) 2) :
    ES M H (f, g) = (perLin M H f + ι M H (perLin M H f)) + (perLin M H g - ι M H (perLin M H g)) := rfl

private theorem ES_apply_ofMul (f g : CuspForm (CohCarrier.GammaH M H) 2) (γ : ↥(CohCarrier.GammaH M H)) :
    ES M H (f, g) (Additive.ofMul γ) =
      periodOf (CohCarrier.GammaH M H) γ f +
        periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) f +
        periodOf (CohCarrier.GammaH M H) γ g -
        periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) g := by
  rw [ES_apply, AddMonoidHom.add_apply, AddMonoidHom.add_apply, AddMonoidHom.sub_apply, ι_apply_ofMul,
    ι_apply_ofMul, perLin_apply_ofMul, perLin_apply_ofMul, perLin_apply_ofMul, perLin_apply_ofMul]
  ring

end Maps

section Injective

private theorem ES_injective : Function.Injective (ES M H) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  rintro ⟨f, g⟩ h0
  have hval : ∀ γ : ↥(CohCarrier.GammaH M H),
      periodOf (CohCarrier.GammaH M H) γ f +
        periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) f +
        periodOf (CohCarrier.GammaH M H) γ g -
        periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) g = 0 := by
    intro γ
    have := congrArg (fun φ : CohCarrier.H1 M H ℂ => φ (Additive.ofMul γ)) h0
    beta_reduce at this
    rwa [ES_apply_ofMul, AddMonoidHom.zero_apply] at this
  have hA : ∀ γ : ↥(CohCarrier.GammaH M H),
      periodOf (CohCarrier.GammaH M H) γ f + periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) f = 0 := by
    intro γ
    have h1 := hval γ
    have h2 := hval (jConjGammaH M H γ)
    rw [jConjGammaH_jConjGammaH] at h2
    linear_combination (h1 + h2) / 2
  have hB : ∀ γ : ↥(CohCarrier.GammaH M H),
      periodOf (CohCarrier.GammaH M H) γ g - periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) g = 0 := by
    intro γ
    have h1 := hval γ
    have h2 := hval (jConjGammaH M H γ)
    rw [jConjGammaH_jConjGammaH] at h2
    linear_combination (h1 - h2) / 2
  have hf : f = 0 := twin_plus M H f hA
  have hg : g = 0 := twin_minus M H g hB
  rw [hf, hg]
  rfl

end Injective

section Range

private theorem ES_range_le :
    LinearMap.range (ES M H) ≤ parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ := by
  rintro _ ⟨⟨f, g⟩, rfl⟩
  have hf : perLin M H f ∈ parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ :=
    periodMapOf_mem_parabolicHoms (CohCarrier.GammaH M H) f
  have hg : perLin M H g ∈ parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ :=
    periodMapOf_mem_parabolicHoms (CohCarrier.GammaH M H) g
  rw [ES_apply]
  exact add_mem (add_mem hf (ι_mem_parabolicHoms M H hf)) (sub_mem hg (ι_mem_parabolicHoms M H hg))

private theorem isCongruenceSubgroup_GammaH : IsCongruenceSubgroup (CohCarrier.GammaH M H) :=
  ⟨M, NeZero.ne _, CuspForm.Gamma_le_GammaH M H⟩

private theorem ES_range :
    LinearMap.range (ES M H) = parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ := by
  obtain ⟨n, b, hb⟩ := exists_basis_parabolicHoms_castAddHom_comp (CohCarrier.GammaH M H)
  obtain ⟨bC, -⟩ := hb ℂ
  haveI : Module.Finite ℂ ↥(parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) := Module.Finite.of_basis bC
  haveI : FiniteDimensional ℂ (CuspForm (CohCarrier.GammaH M H) 2) :=
    CuspForm.finiteDimensional_of_isArithmetic _ 2
  have hP : Module.finrank ℂ ↥(parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) ≤
      2 * Module.finrank ℂ (CuspForm (CohCarrier.GammaH M H) 2) := by
    have hZ := finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup
      (CohCarrier.GammaH M H) (isCongruenceSubgroup_GammaH M H)
    rw [Module.finrank_eq_card_basis b] at hZ
    rw [Module.finrank_eq_card_basis bC]
    exact hZ
  have hr : Module.finrank ℂ ↥(LinearMap.range (ES M H)) =
      2 * Module.finrank ℂ (CuspForm (CohCarrier.GammaH M H) 2) := by
    rw [LinearMap.finrank_range_of_inj (ES_injective M H), Module.finrank_prod, two_mul]
  refine Submodule.eq_of_le_of_finrank_eq (ES_range_le M H) (le_antisymm ?_ ?_)
  · exact Submodule.finrank_mono (ES_range_le M H)
  · rw [hr]; exact hP

end Range

section Equivariance

private theorem ι_heckeT {ℓ : ℕ} (hℓ : ℓ.Prime) (φ : CohCarrier.H1 M H ℂ) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ι M H (CohCarrier.heckeT M H ℓ ℂ φ) = CohCarrier.heckeT M H ℓ ℂ (ι M H φ) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  by_cases hℓM : ℓ ∣ M
  · exact LinearMap.congr_fun (charInvolution_comp_opFamily M H (∅ : Set ℕ) ℂ (Gen.U ℓ hℓ hℓM)) φ
  · exact LinearMap.congr_fun
      (charInvolution_comp_opFamily M H (∅ : Set ℕ) ℂ (Gen.T ℓ hℓ (Set.notMem_empty ℓ) hℓM)) φ

private theorem ι_diamondL (d : (ZMod M)ˣ) (φ : CohCarrier.H1 M H ℂ) :
    ι M H (CohCarrier.diamondL M H ℂ d φ) = CohCarrier.diamondL M H ℂ d (ι M H φ) :=
  LinearMap.congr_fun (charInvolution_comp_opFamily M H (∅ : Set ℕ) ℂ (Gen.dia d)) φ

private theorem perLin_heckeTLinH {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (f : CuspForm (CohCarrier.GammaH M H) 2) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    perLin M H (CuspForm.heckeTLinH 2 hℓ hℓM f) = CohCarrier.heckeT M H ℓ ℂ (perLin M H f) :=
  periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash M H hℓ hℓM
    (CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM)) (CuspForm.gammaLift_apply_11 hℓ hℓM) f _
    (CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM) f)

private theorem perLin_heckeULinH {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f : CuspForm (CohCarrier.GammaH M H) 2) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    perLin M H (CuspForm.heckeULinH 2 q f) = CohCarrier.heckeT M H q ℂ (perLin M H f) :=
  periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU M H hq hqM f _
    (CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hq hqM) f)

private theorem perLin_diamondLinH (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) 2) :
    perLin M H (CuspForm.diamondLinH 2 d f) = CohCarrier.diamondL M H ℂ d (perLin M H f) := by
  rw [CohCarrier.diamondL_eq_diamondRaw M H ℂ d (CuspForm.gammaLift M d) (CuspForm.gamma0Units_gammaLift d)]
  exact periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash M H (CuspForm.gammaLift M d) f _
    (CuspForm.coe_diamondLinH_apply 2 (CuspForm.stableD M H 2) d f)

private theorem ES_heckeTLinH {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (f g : CuspForm (CohCarrier.GammaH M H) 2) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ES M H (CuspForm.heckeTLinH 2 hℓ hℓM f, CuspForm.heckeTLinH 2 hℓ hℓM g) =
      CohCarrier.heckeT M H ℓ ℂ (ES M H (f, g)) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rw [ES_apply, ES_apply, perLin_heckeTLinH, perLin_heckeTLinH, ι_heckeT M H hℓ, ι_heckeT M H hℓ,
    map_add, map_add, map_sub]

private theorem ES_heckeULinH {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f g : CuspForm (CohCarrier.GammaH M H) 2) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ES M H (CuspForm.heckeULinH 2 q f, CuspForm.heckeULinH 2 q g) =
      CohCarrier.heckeT M H q ℂ (ES M H (f, g)) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  rw [ES_apply, ES_apply, perLin_heckeULinH M H hq hqM, perLin_heckeULinH M H hq hqM, ι_heckeT M H hq,
    ι_heckeT M H hq, map_add, map_add, map_sub]

private theorem ES_diamondLinH (d : (ZMod M)ˣ) (f g : CuspForm (CohCarrier.GammaH M H) 2) :
    ES M H (CuspForm.diamondLinH 2 d f, CuspForm.diamondLinH 2 d g) =
      CohCarrier.diamondL M H ℂ d (ES M H (f, g)) := by
  rw [ES_apply, ES_apply, perLin_diamondLinH, perLin_diamondLinH, ι_diamondL, ι_diamondL,
    map_add, map_add, map_sub]

end Equivariance

private theorem main :
    ∃ (J : ↥(CohCarrier.GammaH M H) →* ↥(CohCarrier.GammaH M H))
      (ES : (CuspForm (CohCarrier.GammaH M H) 2 × CuspForm (CohCarrier.GammaH M H) 2)
        →ₗ[ℂ] CohCarrier.H1 M H ℂ),
      (∀ γ : ↥(CohCarrier.GammaH M H), ((J γ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) =
        ModularCurve.Period.jConjSL (γ : SL(2, ℤ))) ∧
      (∀ (f g : CuspForm (CohCarrier.GammaH M H) 2) (γ : ↥(CohCarrier.GammaH M H)),
        ES (f, g) (Additive.ofMul γ) =
          ModularCurve.periodMapOf (CohCarrier.GammaH M H) f (Additive.ofMul γ) +
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) f (Additive.ofMul (J γ)) +
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) g (Additive.ofMul γ) -
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) g (Additive.ofMul (J γ))) ∧
      Function.Injective ES ∧
      LinearMap.range ES = ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ES (CuspForm.heckeTLinH 2 hℓ hℓM f, CuspForm.heckeTLinH 2 hℓ hℓM g) =
          CohCarrier.heckeT M H ℓ ℂ (ES (f, g))) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        haveI : NeZero q := ⟨hq.ne_zero⟩
        ES (CuspForm.heckeULinH 2 q f, CuspForm.heckeULinH 2 q g) =
          CohCarrier.heckeT M H q ℂ (ES (f, g))) ∧
      (∀ (d : (ZMod M)ˣ) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        ES (CuspForm.diamondLinH 2 d f, CuspForm.diamondLinH 2 d g) =
          CohCarrier.diamondL M H ℂ d (ES (f, g))) := by
  refine ⟨jConjGammaH M H, ES M H, fun γ => rfl, ?_, ES_injective M H, ES_range M H,
    fun ℓ hℓ hℓM f g => ES_heckeTLinH M H hℓ hℓM f g,
    fun q hq hqM f g => ES_heckeULinH M H hq hqM f g,
    fun d f g => ES_diamondLinH M H d f g⟩
  intro f g γ
  rw [ES_apply_ofMul, periodMapOf_apply_eq_periodOf, periodMapOf_apply_eq_periodOf,
    periodMapOf_apply_eq_periodOf, periodMapOf_apply_eq_periodOf]

end CohCarrier.ESGammaH

end

open scoped MatrixGroups in

theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ (J : ↥(CohCarrier.GammaH M H) →* ↥(CohCarrier.GammaH M H))
      (ES : (CuspForm (CohCarrier.GammaH M H) 2 × CuspForm (CohCarrier.GammaH M H) 2)
        →ₗ[ℂ] CohCarrier.H1 M H ℂ),
      (∀ γ : ↥(CohCarrier.GammaH M H), ((J γ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) =
        ModularCurve.Period.jConjSL (γ : SL(2, ℤ))) ∧
      (∀ (f g : CuspForm (CohCarrier.GammaH M H) 2) (γ : ↥(CohCarrier.GammaH M H)),
        ES (f, g) (Additive.ofMul γ) =
          ModularCurve.periodMapOf (CohCarrier.GammaH M H) f (Additive.ofMul γ) +
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) f (Additive.ofMul (J γ)) +
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) g (Additive.ofMul γ) -
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) g (Additive.ofMul (J γ))) ∧
      Function.Injective ES ∧
      LinearMap.range ES = ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ES (CuspForm.heckeTLinH 2 hℓ hℓM f, CuspForm.heckeTLinH 2 hℓ hℓM g) =
          CohCarrier.heckeT M H ℓ ℂ (ES (f, g))) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        haveI : NeZero q := ⟨hq.ne_zero⟩
        ES (CuspForm.heckeULinH 2 q f, CuspForm.heckeULinH 2 q g) =
          CohCarrier.heckeT M H q ℂ (ES (f, g))) ∧
      (∀ (d : (ZMod M)ˣ) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        ES (CuspForm.diamondLinH 2 d f, CuspForm.diamondLinH 2 d g) =
          CohCarrier.diamondL M H ℂ d (ES (f, g))) :=
  CohCarrier.ESGammaH.main M H
