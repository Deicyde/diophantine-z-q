/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf (git blob caea4c83b223cf71f0de179190cac4c7b3903ca6, sha256 35de2b3350ed10b8786f1454ce9859b32e3089dd0c11e8f7e809d6c91cf59af9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_ComplexConjugation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_CharInvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_heckeInputsHAlong
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups ModularForm ComplexConjugate

namespace AJHGlue

open CohCarrier ModularCurve UpperHalfPlane Matrix.SpecialLinearGroup AlgebraicCurve

section ConjSide

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

abbrev Lat : Submodule ℤ (Module.Dual ℂ (CuspForm (GammaH M H) 2)) := periodLatticeOf (GammaH M H)

theorem J_smul_I : UpperHalfPlane.J • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_J_smul, UpperHalfPlane.coe_I, Complex.conj_I, neg_neg]

theorem J_smul_J_smul (τ : ℍ) : UpperHalfPlane.J • UpperHalfPlane.J • τ = τ := by
  rw [← mul_smul, ← sq, UpperHalfPlane.J_sq, one_smul]

theorem J_inv_mul_mapGL_mul_J (γ : SL(2, ℤ)) :
    UpperHalfPlane.J⁻¹ * (mapGL ℝ γ : GL (Fin 2) ℝ) * UpperHalfPlane.J =
      (mapGL ℝ (ModularCurve.Period.jConjSL γ) : GL (Fin 2) ℝ) := by
  have hJ : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
    rw [inv_eq_iff_mul_eq_one, ← sq, UpperHalfPlane.J_sq]
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperHalfPlane.J, Matrix.mul_apply, Fin.sum_univ_two, ModularCurve.Period.jConjMat,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.vecMul, dotProduct]

theorem J_smul_sl_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.J • (γ • τ) = ModularCurve.Period.jConjSL γ • (UpperHalfPlane.J • τ) := by
  have hJ : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
    rw [inv_eq_iff_mul_eq_one, ← sq, UpperHalfPlane.J_sq]
  have h := J_inv_mul_mapGL_mul_J γ
  rw [hJ] at h
  have h2 : UpperHalfPlane.J * (mapGL ℝ γ : GL (Fin 2) ℝ) =
      (mapGL ℝ (ModularCurve.Period.jConjSL γ) : GL (Fin 2) ℝ) * UpperHalfPlane.J := by
    rw [← h, mul_assoc, mul_assoc, ← sq, UpperHalfPlane.J_sq, mul_one]
  rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def, ← mul_smul, ← mul_smul]
  exact congrArg (· • τ) h2

theorem jStable : ∀ γ ∈ GammaH M H, ModularCurve.Period.jConjSL γ ∈ GammaH M H :=
  fun _ hγ => CohCarrier.jConjSL_mem_GammaH M H hγ

def conjF (f : CuspForm (GammaH M H) 2) : CuspForm (GammaH M H) 2 :=
  Classical.choose
    (CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem (GammaH M H) (jStable M H) 2 f)

theorem conjF_apply (f : CuspForm (GammaH M H) 2) (τ : ℍ) :
    conjF M H f τ = conj (f (UpperHalfPlane.J • τ)) :=
  Classical.choose_spec
    (CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem (GammaH M H) (jStable M H) 2 f) τ

theorem conjF_add (f g : CuspForm (GammaH M H) 2) : conjF M H (f + g) = conjF M H f + conjF M H g :=
  CuspForm.ext fun τ => by simp only [conjF_apply, CuspForm.add_apply, map_add]

theorem conjF_smul (a : ℂ) (f : CuspForm (GammaH M H) 2) : conjF M H (a • f) = conj a • conjF M H f :=
  CuspForm.ext fun τ => by
    rw [conjF_apply, CuspForm.IsGLPos.smul_apply, CuspForm.IsGLPos.smul_apply, smul_eq_mul, smul_eq_mul,
      map_mul, conjF_apply]

def Rdual (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)) : Module.Dual ℂ (CuspForm (GammaH M H) 2) where
  toFun f := -conj (φ (conjF M H f))
  map_add' f g := by rw [conjF_add, map_add, map_add, neg_add]
  map_smul' a f := by
    show -conj (φ (conjF M H (a • f))) = a • (-conj (φ (conjF M H f)))
    rw [conjF_smul, LinearMap.map_smul, smul_eq_mul, map_mul, Complex.conj_conj, smul_eq_mul, mul_neg]

theorem Rdual_apply (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)) (f : CuspForm (GammaH M H) 2) :
    Rdual M H φ f = -conj (φ (conjF M H f)) := rfl

def R : Module.Dual ℂ (CuspForm (GammaH M H) 2) →+ Module.Dual ℂ (CuspForm (GammaH M H) 2) where
  toFun := Rdual M H
  map_zero' := LinearMap.ext fun f => by
    rw [Rdual_apply, LinearMap.zero_apply, map_zero, neg_zero, LinearMap.zero_apply]
  map_add' φ ψ := LinearMap.ext fun f => by
    simp only [Rdual_apply, LinearMap.add_apply, map_add, neg_add]

theorem R_apply_apply (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)) (f : CuspForm (GammaH M H) 2) :
    R M H φ f = -conj (φ (conjF M H f)) := rfl

theorem eq_R_of_pairing (φ φ' : Module.Dual ℂ (CuspForm (GammaH M H) 2))
    (hpair : ∀ f g : CuspForm (GammaH M H) 2,
      (∀ τ : ℍ, g τ = conj (f (UpperHalfPlane.J • τ))) → φ' g = -conj (φ f)) :
    φ' = R M H φ :=
  LinearMap.ext fun g => by
    rw [R_apply_apply]
    refine hpair (conjF M H g) g fun τ => ?_
    rw [conjF_apply, Complex.conj_conj, J_smul_J_smul]

theorem R_periodOf (δ : ↥(GammaH M H)) :
    R M H (periodOf (GammaH M H) δ) = periodOf (GammaH M H) (jConjGammaH M H δ) := by
  refine LinearMap.ext fun f => ?_
  rw [R_apply_apply]
  show -conj (periodAlongOf (GammaH M H) UpperHalfPlane.I ((δ : SL(2, ℤ)) • UpperHalfPlane.I) (conjF M H f)) =
    periodAlongOf (GammaH M H) UpperHalfPlane.I
      ((ModularCurve.Period.jConjSL (δ : SL(2, ℤ))) • UpperHalfPlane.I) f
  rw [ModularCurve.periodAlongOf_eq_neg_conj_periodAlongOf_J_smul (GammaH M H) f (conjF M H f)
      (conjF_apply M H f), map_neg, Complex.conj_conj, neg_neg, J_smul_sl_smul, J_smul_I]

theorem map_mem_of_forall {T : Module.Dual ℂ (CuspForm (GammaH M H) 2) →+ Module.Dual ℂ (CuspForm (GammaH M H) 2)}
    (hT : ∀ δ : ↥(GammaH M H), T (periodOf (GammaH M H) δ) ∈ Lat M H) :
    ∀ v ∈ Lat M H, T v ∈ Lat M H := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨δ, rfl⟩ := hx
    exact hT δ
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul n x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ n hx

theorem R_mem : ∀ v ∈ Lat M H, R M H v ∈ Lat M H :=
  map_mem_of_forall M H fun δ => by
    rw [R_periodOf]
    exact periodOf_mem_periodLatticeOf _ _

theorem partner_mem (φ φ' : Module.Dual ℂ (CuspForm (GammaH M H) 2))
    (hpair : ∀ f g : CuspForm (GammaH M H) 2,
      (∀ τ : ℍ, g τ = conj (f (UpperHalfPlane.J • τ))) → φ' g = -conj (φ f))
    (hφ : φ ∈ Lat M H) : φ' ∈ Lat M H := by
  rw [eq_R_of_pairing M H φ φ' hpair]
  exact R_mem M H φ hφ

end ConjSide

section Generators



theorem complexEmbedding_comp_algebraMap :
    (complexEmbedding : (AlgebraicClosure ℚ) →ₐ[ℚ] ℂ).toRingHom.comp (algebraMap ℚ (AlgebraicClosure ℚ)) = algebraMap ℚ ℂ :=
  complexEmbedding.comp_algebraMap

theorem coeffMap_complexEmbedding_coeffEmb (z : LaurentSeries ℚ) :
    coeffMap (complexEmbedding : (AlgebraicClosure ℚ) →ₐ[ℚ] ℂ).toRingHom (coeffEmb (AlgebraicClosure ℚ) z) = coeffEmb ℂ z := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr complexEmbedding_comp_algebraMap z

theorem coeffEmb_complex_eq (y : LaurentSeries ℚ) : coeffEmb ℂ y = coeffMap (algebraMap ℚ ℂ) y := rfl

end Generators

section Main



variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem hinC : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; HeckeInputsHAlong ℂ M H ℓ :=
  fun ℓ hℓ => by
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact ModularCurve.heckeInputsHAlong ℂ M H ℓ

theorem mainThm (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (hstT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstU : ∀ (q : ℕ), q.Prime → q ∣ M → ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeULinH 2 q).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstD : ∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    ∃ u : ModularCurve.JH M H →+
        (Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) ⧸ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)),
      Function.Injective u ∧
      (∀ y, IsOfFinAddOrder y → y ∈ u.range) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (x : ModularCurve.JH M H)
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ) x) =
          Submodule.Quotient.mk ((CuspForm.heckeTLinH 2 hℓ hℓM).dualMap φ)) ∧
      (∀ (q : ℕ) (hq : q.Prime), q ∣ M → ∀ (x : ModularCurve.JH M H)
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero q := ⟨hq.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H q) x) =
          Submodule.Quotient.mk ((CuspForm.heckeULinH 2 q).dualMap φ)) ∧
      ∀ (d : (ZMod M)ˣ) (x : ModularCurve.JH M H) (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u (ModularCurve.diamondHBar M H d x) =
          Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ) := by

  obtain ⟨φb, ι, hφb, hιinj, hιtors, hιT, hιg, hιext⟩ :=
    ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex M H

  obtain ⟨v, hvbij, hvT, hvU, hvD, -⟩ :=
    ModularCurve.exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf M H
      (hinC M H) hstT hstU hstD (fun φ φ' hpair hφ => partner_mem M H φ φ' hpair hφ)
  refine ⟨v.comp ι, hvbij.1.comp hιinj, ?_, ?_, ?_, ?_⟩
  ·
    intro y hy
    obtain ⟨z, rfl⟩ := hvbij.2 y
    have hz : IsOfFinAddOrder z := by
      obtain ⟨n, hn, hny⟩ := hy.exists_nsmul_eq_zero
      refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hvbij.1 ?_⟩
      rw [map_nsmul, map_zero]
      exact hny
    obtain ⟨x, rfl⟩ := hιtors z hz
    exact ⟨x, rfl⟩
  ·
    intro ℓ hℓ hℓM x φ hx
    have key := @hιT ℓ ⟨hℓ.ne_zero⟩ (hin.1 ℓ hℓ) (hinC M H ℓ hℓ) x
    rw [AddMonoidHom.comp_apply] at hx ⊢
    rw [key]
    exact hvT ℓ hℓ hℓM (ι x) φ hx
  ·
    intro q hq hqM x φ hx
    have key := @hιT q ⟨hq.ne_zero⟩ (hin.1 q hq) (hinC M H q hq) x
    rw [AddMonoidHom.comp_apply] at hx ⊢
    rw [key]
    exact hvU q hq hqM (ι x) φ hx
  ·
    intro d x φ hx
    have hσd : IsDiamondAutHBar M H d (diamondAutHBar M H d) := hin.isDiamondAutHBar d
    obtain ⟨σ', hσ'⟩ := hιext (diamondAutHBar M H d)
    have hcompat : ∀ y : ↥(xHFunctionFieldBar M H),
        SemilinearAut.ofAlgAut σ' • φb y = φb (SemilinearAut.ofAlgAut (diamondAutHBar M H d) • y) :=
      fun y => by rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul, hσ']
    rw [AddMonoidHom.comp_apply] at hx ⊢
    rw [diamondHBar_apply,
      hιg (SemilinearAut.ofAlgAut (diamondAutHBar M H d)) (SemilinearAut.ofAlgAut σ') hcompat x]
    refine hvD d σ' ?_ (ι x) φ hx

    intro k f g pf pg hf hg hg0 γ hγ hd
    obtain ⟨y, -, hyσ, hyq⟩ := hσd k f g pf pg hf hg hg0 γ hγ hd

    have heC : (⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          ↥(laurentBaseChange ℂ (xHFunctionField M H))) =
        φb ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :=
      Subtype.ext (by rw [hφb]; exact (coeffMap_complexEmbedding_coeffEmb _).symm)
    have step : ((σ' ⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          ↥(laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) =
        coeffMap (algebraMap ℚ ℂ) y := by
      rw [heC, hσ', hφb, hyσ, coeffMap_complexEmbedding_coeffEmb]
      rfl
    rw [step]
    exact hyq

end Main

end AJHGlue

end

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (hstT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstU : ∀ (q : ℕ), q.Prime → q ∣ M → ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeULinH 2 q).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstD : ∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    ∃ u : ModularCurve.JH M H →+
        (Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) ⧸ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)),
      Function.Injective u ∧
      (∀ y, IsOfFinAddOrder y → y ∈ u.range) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (x : ModularCurve.JH M H)
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ) x) =
          Submodule.Quotient.mk ((CuspForm.heckeTLinH 2 hℓ hℓM).dualMap φ)) ∧
      (∀ (q : ℕ) (hq : q.Prime), q ∣ M → ∀ (x : ModularCurve.JH M H)
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero q := ⟨hq.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H q) x) =
          Submodule.Quotient.mk ((CuspForm.heckeULinH 2 q).dualMap φ)) ∧
      ∀ (d : (ZMod M)ˣ) (x : ModularCurve.JH M H) (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u (ModularCurve.diamondHBar M H d x) =
          Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ) :=
  AJHGlue.mainThm M H hin hstT hstU hstD
