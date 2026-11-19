/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar (git blob c10d15c1df789ede2a5eb69d305f0484aad65782, sha256 ba00d8a4c66700cdf139463d11816c134785d581a0d7fe33653bf03c6d27dfd9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpReductionModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpFrobeniusModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_heckeOperatorHAlong
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_heckeDiamondInputsHAll

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace ModularCurve
end ModularCurve
namespace HahnSeries
end HahnSeries
namespace IntermediateField
end IntermediateField
namespace CongruenceSubgroup
end CongruenceSubgroup
namespace UpperHalfPlane
end UpperHalfPlane
namespace P2MW.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar.ES1Sol
end P2MW.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar.ES1Sol

namespace P2MW.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open _root_.AlgebraicCurve
open _root_.ModularCurve hiding laurentBaseChange_mono qExpand_mem_laurentBaseChange
open _root_.HahnSeries
open _root_.IntermediateField
open _root_.CongruenceSubgroup
open _root_.UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise

namespace ES1Sol



abbrev FF (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ)) :
    IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (qExpFunctionFieldC ℚ Γ)

abbrev JJ (Γ : Subgroup SL(2, ℤ)) : Type _ := Pic0 (AlgebraicClosure ℚ) (FF (AlgebraicClosure ℚ) Γ)

example (M : ℕ) : JOne M = JJ (Gamma1 M) := rfl
example (M : ℕ) (H : Subgroup (ZMod M)ˣ) : JH M H = JJ (CohCarrier.GammaH M H) := rfl

section Supply

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem laurentBaseChange_mono {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

theorem qExpand_mem_laurentBaseChange {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ)
    [NeZero n] {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ y ∈ F₀, qExpand ℚ n y ∈ F₁)
    {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    qExpand L n x ∈ laurentBaseChange L F₁ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero,
          ← algebraMap_laurentSeries_eq_single]
        exact (laurentBaseChange L F₁).algebraMap_mem _
      · rw [coeffEmb, ← coeffMap_qExpand]
        exact coeffEmb_mem_laurentBaseChange L (hF z hz)
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

end Supply

section Hecke

variable (L : Type*) [Field L] [Algebra ℚ L]

def gAlpha (Γ : Subgroup SL(2, ℤ)) (t : ℕ) : FF L Γ →ₐ[L] FF L (Γ ⊓ Gamma0 t) :=
  IntermediateField.inclusion (laurentBaseChange_mono L (qExpFunctionFieldC_mono ℚ inf_le_left))

def gBeta (Γ : Subgroup SL(2, ℤ)) (t ℓ : ℕ) [NeZero ℓ]
    (h : ∀ y ∈ qExpFunctionFieldC ℚ Γ, qExpand ℚ ℓ y ∈ qExpFunctionFieldC ℚ (Γ ⊓ Gamma0 t)) :
    FF L Γ →ₐ[L] FF L (Γ ⊓ Gamma0 t) where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L), qExpand_mem_laurentBaseChange L ℓ h x.2⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)
  commutes' a := Subtype.ext <| by
    show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

theorem gAlpha_heq {Γ Γ' : Subgroup SL(2, ℤ)} (e : Γ = Γ') (t : ℕ) :
    HEq (gAlpha L Γ t) (gAlpha L Γ' t) := by
  subst e; rfl

theorem gBeta_heq {Γ Γ' : Subgroup SL(2, ℤ)} (e : Γ = Γ') (t ℓ : ℕ) [NeZero ℓ]
    (h : ∀ y ∈ qExpFunctionFieldC ℚ Γ, qExpand ℚ ℓ y ∈ qExpFunctionFieldC ℚ (Γ ⊓ Gamma0 t))
    (h' : ∀ y ∈ qExpFunctionFieldC ℚ Γ', qExpand ℚ ℓ y ∈ qExpFunctionFieldC ℚ (Γ' ⊓ Gamma0 t)) :
    HEq (gBeta L Γ t ℓ h) (gBeta L Γ' t ℓ h') := by
  subst e; rfl

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

theorem heckeAlphaOneBar_eq : heckeAlphaOneBar L M ℓ = gAlpha L (Gamma1 M) (M * ℓ) := rfl

theorem heckeAlphaHBar_eq : heckeAlphaHBar L M H ℓ = gAlpha L (CohCarrier.GammaH M H) (M * ℓ) := rfl

theorem heckeBetaOneBar_eq' (h0 : HeckeBetaOneDefined M ℓ) :
    heckeBetaOneBar L M ℓ = gBeta L (Gamma1 M) (M * ℓ) ℓ h0 := by
  rw [heckeBetaOneBar_eq M ℓ h0]
  rfl

theorem heckeBetaHBar_eq' (h0 : HeckeBetaHDefined M H ℓ) :
    heckeBetaHBar L M H ℓ = gBeta L (CohCarrier.GammaH M H) (M * ℓ) ℓ h0 := by
  rw [heckeBetaHBar_eq M H ℓ h0]
  rfl

theorem correspondence_heq {Γ Γ' : Subgroup SL(2, ℤ)} (e : Γ = Γ') (t : ℕ)
    (α β : FF L Γ →ₐ[L] FF L (Γ ⊓ Gamma0 t)) (α' β' : FF L Γ' →ₐ[L] FF L (Γ' ⊓ Gamma0 t))
    (eα : HEq α α') (eβ : HEq β β')
    [i : HasPrincipalDivisors L (FF L (Γ ⊓ Gamma0 t))]
    [i' : HasPrincipalDivisors L (FF L (Γ' ⊓ Gamma0 t))]
    (hβ : β.toRingHom.IsIntegral) (hα : α.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong L β hβ) (hfin : FiniteAlong L α)
    (hN : NormFormulaAlong L α hfin)
    (hβ' : β'.toRingHom.IsIntegral) (hα' : α'.toRingHom.IsIntegral)
    (hFI' : FundamentalIdentityAlong L β' hβ') (hfin' : FiniteAlong L α')
    (hN' : NormFormulaAlong L α' hfin') :
    HEq (⇑(Pic0.correspondence β α hβ hα hFI hfin hN))
      (⇑(Pic0.correspondence β' α' hβ' hα' hFI' hfin' hN')) := by
  subst e
  cases eα
  cases eβ
  rfl

theorem heckeAlpha_heq : HEq (heckeAlphaHBar L M ⊥ ℓ) (heckeAlphaOneBar L M ℓ) := by
  rw [heckeAlphaHBar_eq, heckeAlphaOneBar_eq]
  exact gAlpha_heq L (GammaH_bot M) _

theorem heckeBeta_heq (h0 : HeckeBetaHDefined M ⊥ ℓ) (h0' : HeckeBetaOneDefined M ℓ) :
    HEq (heckeBetaHBar L M ⊥ ℓ) (heckeBetaOneBar L M ℓ) := by
  rw [heckeBetaHBar_eq' L M ⊥ ℓ h0, heckeBetaOneBar_eq' L M ℓ h0']
  exact gBeta_heq L (GammaH_bot M) _ _ _ _

theorem heckeOperator_heq (hinH : HeckeInputsHAlong L M ⊥ ℓ) (hin1 : HeckeInputsOneAlong L M ℓ) :
    HEq (⇑(heckeOperatorHAlong L M ⊥ ℓ)) (⇑(heckeOperatorOneAlong L M ℓ)) := by
  obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := hinH
  obtain ⟨h0', hα', hβ', hP', hfin', hFI', hN'⟩ := hin1
  rw [heckeOperatorHAlong_eq h0 hα hβ hFI hfin hN, heckeOperatorOneAlong_eq h0' hα' hβ' hFI' hfin' hN']
  exact correspondence_heq L (GammaH_bot M) (M * ℓ) (heckeAlphaHBar L M ⊥ ℓ) (heckeBetaHBar L M ⊥ ℓ)
    (heckeAlphaOneBar L M ℓ) (heckeBetaOneBar L M ℓ) (heckeAlpha_heq L M ℓ)
    (heckeBeta_heq L M ℓ h0 h0') (i := hP) (i' := hP') hβ hα hFI hfin hN hβ' hα' hFI' hfin' hN'

end Hecke

section Diamond

def IsDiaGen (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (d : (ZMod M)ˣ) (σ : FF (AlgebraicClosure ℚ) Γ ≃ₐ[(AlgebraicClosure ℚ)] FF (AlgebraicClosure ℚ) Γ) : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)), γ ∈ Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
      ∃ y : LaurentSeries ℚ, y ∈ qExpFunctionFieldC ℚ Γ ∧
        ((σ ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : FF (AlgebraicClosure ℚ) Γ) :
            LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y ∧
        coeffMap (algebraMap ℚ ℂ) y *
            HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ)))

theorem isDiamondAutHBar_iff_isDiaGen (M : ℕ) (H : Subgroup (ZMod M)ˣ) (d : (ZMod M)ˣ)
    (σ : xHFunctionFieldBar M H ≃ₐ[(AlgebraicClosure ℚ)] xHFunctionFieldBar M H) :
    IsDiamondAutHBar M H d σ ↔ IsDiaGen M (CohCarrier.GammaH M H) d σ :=
  Iff.rfl

theorem exists_heq_isDiaGen (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {Γ' : Subgroup SL(2, ℤ)}
    (e : CohCarrier.GammaH M H = Γ') (d : (ZMod M)ˣ) :
    ∃ σ' : FF (AlgebraicClosure ℚ) Γ' ≃ₐ[(AlgebraicClosure ℚ)] FF (AlgebraicClosure ℚ) Γ', HEq (diamondAutHBar M H d) σ' ∧ IsDiaGen M Γ' d σ' := by
  subst e
  exact ⟨_, HEq.rfl, (ModularCurve.heckeDiamondInputsHAll M H).isDiamondAutHBar d⟩

variable {M : ℕ}

abbrev Γ1 (M : ℕ) : Subgroup (GL (Fin 2) ℝ) := ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  rw [← GammaH_bot M]
  exact translation_mem_GammaH M ⊥

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ1 M).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 (M := M))]
  exact AddSubgroup.mem_zmultiples _

theorem conj_mem_Gamma1 {γ δ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hδ : δ ∈ Gamma1 M) :
    γ * δ * γ⁻¹ ∈ Gamma1 M := by
  rw [← GammaH_bot M] at hδ ⊢
  exact CohCarrier.conj_mem_GammaH M ⊥ ⟨γ, hγ⟩ ⟨δ, hδ⟩

theorem le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    Γ1 M ≤ ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ • Γ1 M := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨γ * δ * γ⁻¹, conj_mem_Gamma1 hγ hδ, by simp; rfl⟩

def slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (Γ1 M) k) :
    ModularForm (Γ1 M) k :=
  restrictForm (le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

@[scoped simp]
theorem coe_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (Γ1 M) k) :
    ⇑(slashForm γ hγ f) = ⇑f ∣[k] (γ : GL (Fin 2) ℝ) := rfl

theorem slashForm_slashForm {k : ℤ} (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hδ : δ ∈ Gamma0 M)
    (f : ModularForm (Γ1 M) k) :
    slashForm δ hδ (slashForm γ hγ f) = slashForm (γ * δ) (mul_mem hγ hδ) f := by
  ext τ
  simp only [coe_slashForm, map_mul, SlashAction.slash_mul]

theorem slashForm_of_mem {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγ1 : γ ∈ Gamma1 M)
    (f : ModularForm (Γ1 M) k) : slashForm γ hγ f = f := by
  ext τ
  exact congrFun (SlashInvariantForm.slash_action_eqn f _
    (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hγ1)) τ

theorem slashForm_one {k : ℤ} (f : ModularForm (Γ1 M) k) : slashForm 1 (one_mem _) f = f :=
  slashForm_of_mem 1 _ (one_mem _) f

theorem slashForm_congr {k : ℤ} {γ γ' : SL(2, ℤ)} (h : γ = γ') (hγ : γ ∈ Gamma0 M) (hγ' : γ' ∈ Gamma0 M)
    (f : ModularForm (Γ1 M) k) : slashForm γ hγ f = slashForm γ' hγ' f := by
  subst h; rfl

theorem slashForm_inv_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (Γ1 M) k) :
    slashForm γ⁻¹ (inv_mem hγ) (slashForm γ hγ f) = f := by
  rw [slashForm_slashForm, slashForm_congr (mul_inv_cancel γ) _ (one_mem _), slashForm_one]

theorem slashForm_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {f : ModularForm (Γ1 M) k}
    (hf : f ≠ 0) : slashForm γ hγ f ≠ 0 := by
  intro h
  apply hf
  rw [← slashForm_inv_slashForm γ hγ f, h]
  ext τ
  simp [coe_slashForm]

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (Γ1 M) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

theorem ιC_injective : Function.Injective ιC :=
  RingHom.injective _

theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    ιC (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem qC_ιC_ne_zero {k : ℤ} {g : ModularForm (Γ1 M) k} {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← ιC_intSeriesC hg]
  exact (map_ne_zero_iff _ ιC_injective).mpr hg0

theorem ne_zero_of_intSeriesC_ne_zero {k : ℤ} {g : ModularForm (Γ1 M) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 :=
  fun h => qC_ιC_ne_zero hg hg0 ((qC_eq_zero_iff g).mpr h)

theorem qC_slashForm_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {g : ModularForm (Γ1 M) k}
    {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    qC (slashForm γ hγ g) ≠ 0 := fun h =>
  slashForm_ne_zero γ hγ (ne_zero_of_intSeriesC_ne_zero hg hg0) ((qC_eq_zero_iff _).mp h)

def iota (Γ : Subgroup SL(2, ℤ)) : qExpFunctionFieldC ℚ Γ →+* FF (AlgebraicClosure ℚ) Γ where
  toFun y := ⟨coeffEmb (AlgebraicClosure ℚ) (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) y.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem coeffEmb_algebraMap (c : ℚ) :
    coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (algebraMap ℚ (AlgebraicClosure ℚ) c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]

variable [NeZero M]

theorem eq_diamondAutBar (hin : HeckeDiamondInputsAll M) {d : ℕ} (hd : d.Coprime M)
    (σ' : FF (AlgebraicClosure ℚ) (Gamma1 M) ≃ₐ[(AlgebraicClosure ℚ)] FF (AlgebraicClosure ℚ) (Gamma1 M))
    (hσ' : IsDiaGen M (Gamma1 M) (ZMod.unitOfCoprime d hd) σ') : σ' = diamondAutBar M d := by
  obtain ⟨hex, hexb⟩ := hin.2 d hd
  have hda : IsDiamondAut M d (diamondAut M d) := isDiamondAut_diamondAut hex
  have hbc : IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut M d) (diamondAutBar M d) :=
    isBaseChangeAutOf_baseChangeAut hexb

  obtain ⟨γd, hγd⟩ := CohCarrier.gamma0Units_surjective M (ZMod.unitOfCoprime d hd)⁻¹
  have hγ : (γd : SL(2, ℤ)) ∈ Gamma0 M := γd.2
  have hγ00 : (((γd : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    have h1 : (CohCarrier.gamma0Units M γd)⁻¹ = ZMod.unitOfCoprime d hd := by rw [hγd, inv_inv]
    have h2 : ((CohCarrier.gamma0Units M γd)⁻¹ : (ZMod M)ˣ).val = ((d : ℕ) : ZMod M) := by
      rw [h1, ZMod.coe_unitOfCoprime]
    exact h2
  have hγ00' : (((γd : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = ((ZMod.unitOfCoprime d hd : (ZMod M)ˣ) : ZMod M) := by
    rw [hγ00, ZMod.coe_unitOfCoprime]

  set F₀ := qExpFunctionFieldC ℚ (Gamma1 M) with hF₀
  set σ₀ : F₀ ≃ₐ[ℚ] F₀ := diamondAut M d with hσ₀
  let φ₁ : F₀ →+* LaurentSeries (AlgebraicClosure ℚ) :=
    (SubringClass.subtype (FF (AlgebraicClosure ℚ) (Gamma1 M))).comp
      (σ'.toRingEquiv.toRingHom.comp (iota (Gamma1 M)))
  let φ₂ : F₀ →+* LaurentSeries (AlgebraicClosure ℚ) :=
    (coeffEmb (AlgebraicClosure ℚ)).comp ((SubringClass.subtype F₀).comp σ₀.toRingEquiv.toRingHom)
  have φ₁def : ∀ y : F₀, φ₁ y = ((σ' (iota (Gamma1 M) y) : FF (AlgebraicClosure ℚ) (Gamma1 M)) : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun _ => rfl
  have φ₂def : ∀ y : F₀, φ₂ y = coeffEmb (AlgebraicClosure ℚ) ((σ₀ y : F₀) : LaurentSeries ℚ) := fun _ => rfl
  have hφ : ∀ (x : LaurentSeries ℚ) (hx : x ∈ F₀), φ₁ ⟨x, hx⟩ = φ₂ ⟨x, hx⟩ := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
        rw [φ₁def, φ₂def]
        obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
        obtain ⟨w, hw, hσw, hwslash⟩ := hσ' k f g pf pg hf hg hg0 γd hγ hγ00'
        have hda' := hda.2 k f g pf pg hf hg hg0 γd hγ hγ00
        have hQ : qC (⇑(slashForm (γd : SL(2, ℤ)) hγ g)) ≠ 0 := qC_slashForm_ne_zero _ hγ hg hg0
        have hcancel : ιC w = ιC ((σ₀ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
            div_mem_qExpFunctionFieldC f g hf hg hg0⟩ : F₀) : LaurentSeries ℚ) := by
          apply mul_right_cancel₀ hQ
          exact hwslash.trans hda'.symm
        have hw' : w = ((σ₀ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
            div_mem_qExpFunctionFieldC f g hf hg hg0⟩ : F₀) : LaurentSeries ℚ) := ιC_injective hcancel
        rw [← hw']
        exact hσw
    | algebraMap c =>
        have key : ∀ y : F₀, (y : LaurentSeries ℚ) = (c : LaurentSeries ℚ) → φ₁ y = φ₂ y := by
          intro y hy
          have : y = (c : F₀) := Subtype.ext (hy.trans (SubfieldClass.coe_ratCast F₀ c).symm)
          rw [this, map_ratCast, map_ratCast]
        exact key _ (eq_ratCast _ c)
    | add x y hx hy ihx ihy =>
        show φ₁ (⟨x, hx⟩ + ⟨y, hy⟩) = φ₂ (⟨x, hx⟩ + ⟨y, hy⟩)
        rw [map_add, map_add, ihx, ihy]
    | inv x hx ih =>
        show φ₁ (⟨x, hx⟩⁻¹) = φ₂ (⟨x, hx⟩⁻¹)
        rw [map_inv₀, map_inv₀, ih]
    | mul x y hx hy ihx ihy =>
        show φ₁ (⟨x, hx⟩ * ⟨y, hy⟩) = φ₂ (⟨x, hx⟩ * ⟨y, hy⟩)
        rw [map_mul, map_mul, ihx, ihy]
  have hσ'bc : IsBaseChangeAutOf (AlgebraicClosure ℚ) σ₀ σ' := fun y => by
    have := hφ y.1 y.2
    rw [φ₁def, φ₂def] at this
    exact this

  apply AlgEquiv.ext
  intro z
  obtain ⟨z, hz⟩ := z
  induction hz using IntermediateField.adjoin_induction with
  | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact Subtype.ext ((hσ'bc ⟨y, hy⟩).trans (hbc ⟨y, hy⟩).symm)
  | algebraMap c =>
      have : (⟨algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c, IntermediateField.algebraMap_mem _ c⟩ :
          FF (AlgebraicClosure ℚ) (Gamma1 M)) = algebraMap (AlgebraicClosure ℚ) (FF (AlgebraicClosure ℚ) (Gamma1 M)) c := rfl
      rw [this, AlgEquiv.commutes]
      exact ((diamondAutBar M d).commutes c).symm
  | add x y hx hy ihx ihy =>
      show σ' (⟨x, hx⟩ + ⟨y, hy⟩) = diamondAutBar M d (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
      rfl
  | inv x hx ih =>
      show σ' (⟨x, hx⟩⁻¹) = diamondAutBar M d (⟨x, hx⟩⁻¹)
      rw [map_inv₀, map_inv₀, ih]
      rfl
  | mul x y hx hy ihx ihy =>
      show σ' (⟨x, hx⟩ * ⟨y, hy⟩) = diamondAutBar M d (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]
      rfl

theorem diamondAut_heq (hin : HeckeDiamondInputsAll M) {d : ℕ} (hd : d.Coprime M) :
    HEq (diamondAutHBar M ⊥ (ZMod.unitOfCoprime d hd)) (diamondAutBar M d) := by
  obtain ⟨σ', hσ', hgen⟩ := exists_heq_isDiaGen M ⊥ (GammaH_bot M) (ZMod.unitOfCoprime d hd)
  exact hσ'.trans (heq_of_eq (eq_diamondAutBar hin hd σ' hgen))

end Diamond

section Assembly

def ESRel (A : ValuationSubring (AlgebraicClosure ℚ)) (Γ : Subgroup SL(2, ℤ)) (ℓ : ℕ) [Fact ℓ.Prime]
    [CharP (IsLocalRing.ResidueField A) ℓ] (T δ : JJ Γ → JJ Γ) (z : JJ Γ) : Prop :=
  reductionQExpModL A Γ (T z) =
    qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A) Γ ℓ (reductionQExpModL A Γ (δ z)) +
      qExpFrobeniusPullbackModL (IsLocalRing.ResidueField A) Γ ℓ (reductionQExpModL A Γ z)

theorem esRel_transport (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime]
    [CharP (IsLocalRing.ResidueField A) ℓ] {Γ Γ' : Subgroup SL(2, ℤ)} (e : Γ = Γ')
    {T δ : JJ Γ → JJ Γ} {T' δ' : JJ Γ' → JJ Γ'} (hT : HEq T T') (hδ : HEq δ δ')
    (h : ReductionInputsQExpModL A Γ → ∀ z, ESRel A Γ ℓ T δ z)
    (hΓ' : ReductionInputsQExpModL A Γ') (z : JJ Γ') : ESRel A Γ' ℓ T' δ' z := by
  subst e
  cases hT
  cases hδ
  exact h hΓ' z

theorem smul_heq {Γ Γ' : Subgroup SL(2, ℤ)} (e : Γ = Γ') (σ : FF (AlgebraicClosure ℚ) Γ ≃ₐ[(AlgebraicClosure ℚ)] FF (AlgebraicClosure ℚ) Γ)
    (σ' : FF (AlgebraicClosure ℚ) Γ' ≃ₐ[(AlgebraicClosure ℚ)] FF (AlgebraicClosure ℚ) Γ') (h : HEq σ σ') :
    HEq (fun z : JJ Γ => SemilinearAut.ofAlgAut σ • z)
      (fun z : JJ Γ' => SemilinearAut.ofAlgAut σ' • z) := by
  subst e
  cases h
  rfl

end Assembly

end ES1Sol
open scoped _root_.P2MW.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar.ES1Sol

open ES1Sol in
theorem solution (M : ℕ) [NeZero M]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (hin : ModularCurve.HeckeDiamondInputsAll M)
    (h : ModularCurve.ReductionInputsQExpModL A (CongruenceSubgroup.Gamma1 M))
    (z : ModularCurve.JOne M) :
    ModularCurve.reductionQExpModL A (CongruenceSubgroup.Gamma1 M)
        (ModularCurve.heckeOperatorOneBar M ⟨ℓ, Fact.out⟩ z) =
      ModularCurve.qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A)
          (CongruenceSubgroup.Gamma1 M) ℓ
          (ModularCurve.reductionQExpModL A (CongruenceSubgroup.Gamma1 M)
            (ModularCurve.diamondOneBar M ℓ z))
        + ModularCurve.qExpFrobeniusPullbackModL (IsLocalRing.ResidueField A)
            (CongruenceSubgroup.Gamma1 M) ℓ
            (ModularCurve.reductionQExpModL A (CongruenceSubgroup.Gamma1 M) z) := by
  have hcop : ℓ.Coprime M := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM
  have hin1 : HeckeInputsOneAlong (AlgebraicClosure ℚ) M ℓ := hin.1 ⟨ℓ, Fact.out⟩
  have hinH : HeckeInputsHAlong (AlgebraicClosure ℚ) M ⊥ ℓ :=
    (ModularCurve.heckeDiamondInputsHAll M ⊥).heckeInputsHAlong ℓ Fact.out
  have key : ∀ (hΓ : ReductionInputsQExpModL A (CohCarrier.GammaH M ⊥)) (w : JH M ⊥),
      ESRel A (CohCarrier.GammaH M ⊥) ℓ
        (fun w : JH M ⊥ => heckeOperatorHAlong (AlgebraicClosure ℚ) M ⊥ ℓ w)
        (fun w : JH M ⊥ =>
          SemilinearAut.ofAlgAut (diamondAutHBar M ⊥ (ZMod.unitOfCoprime ℓ hcop)) • w) w :=
    fun hΓ w => ModularCurve.reductionQExpModL_gammaH_heckeOperatorHAlong M ⊥ hℓM A hA
      (ModularCurve.heckeDiamondInputsHAll M ⊥) hΓ w
  have hT : HEq (fun w : JH M ⊥ => heckeOperatorHAlong (AlgebraicClosure ℚ) M ⊥ ℓ w)
      (fun z : JOne M => heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ z) :=
    heckeOperator_heq (AlgebraicClosure ℚ) M ℓ hinH hin1
  have hδ : HEq (fun w : JH M ⊥ =>
        SemilinearAut.ofAlgAut (diamondAutHBar M ⊥ (ZMod.unitOfCoprime ℓ hcop)) • w)
      (fun z : JOne M => SemilinearAut.ofAlgAut (diamondAutBar M ℓ) • z) :=
    smul_heq (GammaH_bot M) _ _ (diamondAut_heq hin hcop)
  exact esRel_transport A ℓ (GammaH_bot M) hT hδ key h z
