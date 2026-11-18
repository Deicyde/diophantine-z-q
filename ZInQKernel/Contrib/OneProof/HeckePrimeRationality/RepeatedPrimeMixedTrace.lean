import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.MixedWeightThreeDistribution
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.RepeatedPrimeProductTrace

/-!
# Repeated-prime trace of mixed weight-three products

Let `p` be prime with `p ∣ ℓ`. For the actual normalized trace from `Γ(pℓ)` to `Γ(ℓ)` in weight
three and the actual mixed forms `x_P λ_Q` (`crossForm`), this file proves that the trace lies in

  `lowerMixedSpan ℓ ⊔ trace(classSeriesSpan (pℓ))`,

where `lowerMixedSpan ℓ` is spanned by the level-`ℓ` mixed forms and `classSeriesSpan` is the span of
the convergent weight-three congruence-class series forms. The statement is proved:

* unconditionally when `P ≡ 0 (mod p)` (`trace_cross_first_zero`), and when `P` is nonzero modulo
  `p` with `Q ≡ σ P`, `σ ∈ {0, 1, -1}` (`trace_cross_slope_small`), using the weight-three
  distribution congruences;
* for pairs independent modulo `p`, by reduction to dependent pairs (`trace_cross_independent`);
* for all labels when `p ∈ {2, 3}` (`trace_cross_mem_small_prime`);
* for all labels and all `p`, given the slope-`σ` statement for every `σ`
  (`trace_cross_mem_of_slopes`).

The trace of the series span is not identified here.
-/

noncomputable section
set_option autoImplicit false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.RepeatedPrimeMixedTrace

open TorsionWeierstrassData TorsionWeightThree MixedWeightThreeAddition MixedWeightThreeDistribution
open DivisionEisensteinLevelMaps DivisionEisensteinLowerClosure RepeatedPrimeProductTrace
open AllLevelForms AllLevelPrincipal
open ThetaFiveTorsion (act act_mul act_one)

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-! ### Weight-three level maps -/

/-- Restriction of weight-three forms to a smaller principal group. -/
def restriction3 (N M : ℕ) (hNM : N ∣ M) : Weight N 3 →ₗ[ℂ] Weight M 3 :=
  _root_.ModularForm.restrictₗ 3 ℂ (principal_group_le hNM)

theorem restriction3_apply (N M : ℕ) (hNM : N ∣ M) (f : Weight N 3) (τ : ℍ) :
    restriction3 N M hNM f τ = f τ := rfl

/-- The actual normalized weight-three trace. -/
def normalizedTrace3 (N M : ℕ) (hM : 0 < M) : Weight M 3 →ₗ[ℂ] Weight N 3 := by
  let : NeZero M := ⟨hM.ne'⟩
  exact ((traceIndex N M : ℂ)⁻¹) • _root_.ModularForm.traceₗ (ΓP N)

theorem normalizedTrace3_apply (N M : ℕ) [NeZero M] (hM : 0 < M) (f : Weight M 3) :
    normalizedTrace3 N M hM f = ((traceIndex N M : ℂ)⁻¹) • _root_.ModularForm.trace (ΓP N) f := by
  let : NeZero M := ⟨hM.ne'⟩
  rfl

theorem normalizedTrace3_restriction {N M : ℕ} (hM : 0 < M) (hNM : N ∣ M) (f : Weight N 3) :
    normalizedTrace3 N M hM (restriction3 N M hNM f) = f := by
  let : NeZero M := ⟨hM.ne'⟩
  have hidx : (traceIndex N M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (traceIndex_ne_zero N M hM)
  change (traceIndex N M : ℂ)⁻¹ •
    _root_.ModularForm.traceₗ (ΓP N) (_root_.ModularForm.restrict (principal_group_le hNM) f) = f
  rw [_root_.ModularForm.traceₗ_restrict]
  change (traceIndex N M : ℂ)⁻¹ • ((traceIndex N M : ℂ) • f) = f
  rw [smul_smul, inv_mul_cancel₀ hidx, one_smul]

/-! ### Covariance and congruence of mixed forms -/

/-- The weight-one function `λ_v`, with the zero convention. -/
def Lam (M : ℕ) (v : ℤ × ℤ) : ℍ → ℂ := fun τ => lambdaValue M v.1 v.2 τ

theorem Lam_slash {M : ℕ} (hM : 0 < M) (γ : SL(2, ℤ)) (v : ℤ × ℤ) :
    Lam M v ∣[(1 : ℤ)] γ = Lam M (act v γ) := by
  funext τ
  rw [ModularForm.SL_slash_apply]
  by_cases hg : Good M v
  · have hg' := good_act hg γ
    have h1 : ¬ ((M : ℤ) ∣ v.1 ∧ (M : ℤ) ∣ v.2) := hg
    have h2 : ¬ ((M : ℤ) ∣ (act v γ).1 ∧ (M : ℤ) ∣ (act v γ).2) := hg'
    have hF := congrFun (F_slash hM γ v hg) τ
    rw [ModularForm.SL_slash_apply] at hF
    simp only [Lam, lambdaValue, TorsionDistributionTwo.reg_of_good h1,
      TorsionDistributionTwo.reg_of_good h2]
    rw [mul_assoc]
    congr 1
  · have hb : (M : ℤ) ∣ v.1 ∧ (M : ℤ) ∣ v.2 := not_not.mp hg
    have hb' : (M : ℤ) ∣ (act v γ).1 ∧ (M : ℤ) ∣ (act v γ).2 := by
      by_contra h
      exact hg (by
        have := good_act (v := act v γ) h γ⁻¹
        rw [act_mul, mul_inv_cancel, act_one] at this
        exact this)
    simp only [Lam, lambdaValue, TorsionDistributionTwo.reg_of_bad hb,
      TorsionDistributionTwo.reg_of_bad hb', mul_zero, zero_mul]

/-- The mixed function `x_U λ_V`. -/
def crossFun (M : ℕ) (U V : ℤ × ℤ) : ℍ → ℂ := fun τ => xValue M U.1 U.2 τ * lambdaValue M V.1 V.2 τ

theorem crossFun_slash {M : ℕ} (hM : 0 < M) (γ : SL(2, ℤ)) (U V : ℤ × ℤ) :
    crossFun M U V ∣[(3 : ℤ)] γ = crossFun M (act U γ) (act V γ) := by
  have he : ∀ U V : ℤ × ℤ, crossFun M U V = WeierstrassForms.X M U * Lam M V := fun _ _ => rfl
  rw [he, he, show (3 : ℤ) = 2 + 1 by norm_num, ModularForm.mul_slash_SL2,
    WeierstrassForms.X_slash hM, Lam_slash hM]

theorem coe_crossForm (M : ℕ) (hM : 0 < M) (U V : ℤ × ℤ) :
    ⇑(crossForm M hM U.1 U.2 V.1 V.2) = crossFun M U V :=
  funext fun τ => crossForm_apply M hM _ _ _ _ τ

theorem xValue_congr {M : ℕ} (hM : 0 < M) {a b c d : ℤ} (h1 : (M : ℤ) ∣ a - c)
    (h2 : (M : ℤ) ∣ b - d) (τ : ℍ) : xValue M a b τ = xValue M c d τ := by
  obtain ⟨m, hm⟩ := h1
  obtain ⟨k, hk⟩ := h2
  rw [show a = c + M * m by linarith, show b = d + M * k by linarith,
    WeierstrassDistributionNat.xValue_shift hM]

theorem lambdaValue_congr {M : ℕ} [NeZero M] {a b c d : ℤ} (h1 : (M : ℤ) ∣ a - c)
    (h2 : (M : ℤ) ∣ b - d) (τ : ℍ) : lambdaValue M a b τ = lambdaValue M c d τ := by
  obtain ⟨m, hm⟩ := h1
  obtain ⟨k, hk⟩ := h2
  unfold lambdaValue
  rw [show a = c + M * m by linarith, show b = d + M * k by linarith,
    TorsionFourierComparison.reg_shift]

theorem crossForm_congr {M : ℕ} (hM : 0 < M) {U V U' V' : ℤ × ℤ}
    (hU : CongrN M U U') (hV : CongrN M V V') :
    crossForm M hM U.1 U.2 V.1 V.2 = crossForm M hM U'.1 U'.2 V'.1 V'.2 := by
  have : NeZero M := ⟨hM.ne'⟩
  apply DFunLike.ext
  intro τ
  rw [crossForm_apply, crossForm_apply, xValue_congr hM hU.1 hU.2, lambdaValue_congr hV.1 hV.2]

theorem crossForm_neg_right (M : ℕ) (hM : 0 < M) (u v u' v' : ℤ) :
    crossForm M hM u v (-u') (-v') = -crossForm M hM u v u' v' := by
  have : NeZero M := ⟨hM.ne'⟩
  apply DFunLike.ext
  intro τ
  change _ = -(crossForm M hM u v u' v' τ)
  rw [crossForm_apply, crossForm_apply]
  unfold lambdaValue
  rw [TorsionFourierComparison.reg_neg]
  ring

/-! ### Trace constancy along principal moves -/

theorem quotientFunc_cross_right_shift (N M : ℕ) (hM : 0 < M) (U V : ℤ × ℤ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N)
    (q : (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)) :
    let g : (ΓP N) := ⟨mapGL ℝ γ, Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩⟩
    let _ := mapped_principal_subgroup_normal N M
    SlashInvariantForm.quotientFunc
        (crossForm M hM (act U γ).1 (act U γ).2 (act V γ).1 (act V γ).2) q =
      SlashInvariantForm.quotientFunc (crossForm M hM U.1 U.2 V.1 V.2)
        (MulOpposite.op g⁻¹ • q) := by
  let g : (ΓP N) := ⟨mapGL ℝ γ, Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩⟩
  let _ := mapped_principal_subgroup_normal N M
  change SlashInvariantForm.quotientFunc
      (crossForm M hM (act U γ).1 (act U γ).2 (act V γ).1 (act V γ).2) q =
    SlashInvariantForm.quotientFunc (crossForm M hM U.1 U.2 V.1 V.2) (MulOpposite.op g⁻¹ • q)
  have hseries : ⇑(crossForm M hM (act U γ).1 (act U γ).2 (act V γ).1 (act V γ).2) =
      (⇑(crossForm M hM U.1 U.2 V.1 V.2) : ℍ → ℂ) ∣[(3 : ℤ)] (mapGL ℝ γ) := by
    have h := crossFun_slash hM γ U V
    rw [ModularForm.SL_slash] at h
    rw [coe_crossForm, coe_crossForm]
    exact h.symm
  induction q using QuotientGroup.induction_on' with
  | H r =>
    rw [MulAction.Quotient.smul_coe, SlashInvariantForm.quotientFunc_mk,
      SlashInvariantForm.quotientFunc_mk, hseries, ← SlashAction.slash_mul]
    simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Subgroup.coe_mul,
      Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv, g]

theorem normalizedTrace3_cross_SL (N M : ℕ) (hM : 0 < M) (U V : ℤ × ℤ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N) :
    normalizedTrace3 N M hM (crossForm M hM (act U γ).1 (act U γ).2 (act V γ).1 (act V γ).2) =
      normalizedTrace3 N M hM (crossForm M hM U.1 U.2 V.1 V.2) := by
  classical
  let : NeZero M := ⟨hM.ne'⟩
  let _ := mapped_principal_subgroup_normal N M
  let Q := (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)
  let : Fintype Q := Fintype.ofFinite Q
  let g : (ΓP N) := ⟨mapGL ℝ γ, Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩⟩
  rw [normalizedTrace3_apply, normalizedTrace3_apply]
  apply congrArg (fun f : Weight N 3 => (traceIndex N M : ℂ)⁻¹ • f)
  apply DFunLike.coe_injective
  rw [_root_.ModularForm.coe_trace, _root_.ModularForm.coe_trace]
  have he : ∀ q : Q,
      SlashInvariantForm.quotientFunc
          (crossForm M hM (act U γ).1 (act U γ).2 (act V γ).1 (act V γ).2) q =
        SlashInvariantForm.quotientFunc (crossForm M hM U.1 U.2 V.1 V.2)
          (MulOpposite.op g⁻¹ • q) := fun q =>
    quotientFunc_cross_right_shift N M hM U V γ hγ q
  simp_rw [he]
  exact Equiv.sum_comp (MulAction.toPerm (MulOpposite.op g⁻¹))
    (SlashInvariantForm.quotientFunc (crossForm M hM U.1 U.2 V.1 V.2))

/-- Trace of a mixed form at labels congruent to a principal move of `(U, V)`. -/
theorem normalizedTrace3_cross_move (N M : ℕ) (hM : 0 < M) (U V U' V' : ℤ × ℤ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N) (hU : CongrN M (act U γ) U') (hV : CongrN M (act V γ) V') :
    normalizedTrace3 N M hM (crossForm M hM U'.1 U'.2 V'.1 V'.2) =
      normalizedTrace3 N M hM (crossForm M hM U.1 U.2 V.1 V.2) := by
  rw [← crossForm_congr hM hU hV]
  exact normalizedTrace3_cross_SL N M hM U V γ hγ

/-! ### Target spaces -/

/-- The span of the level-`ℓ` mixed forms. -/
def lowerMixedSpan (ell : ℕ) (hl : 0 < ell) : Submodule ℂ (Weight ell 3) :=
  Submodule.span ℂ (Set.range fun w : (ℤ × ℤ) × (ℤ × ℤ) =>
    crossForm ell hl w.1.1 w.1.2 w.2.1 w.2.2)

/-- The lower target: lower mixed forms plus the trace of the upper class-series span. -/
def target (p ell : ℕ) (hl : 0 < ell) (hM : 0 < p * ell) : Submodule ℂ (Weight ell 3) :=
  lowerMixedSpan ell hl ⊔ (classSeriesSpan (p * ell) hM).map (normalizedTrace3 ell (p * ell) hM)

/-- The upper space: restricted lower mixed forms plus the upper class-series span. -/
def upperGood (p ell : ℕ) (hl : 0 < ell) (hM : 0 < p * ell) : Submodule ℂ (Weight (p * ell) 3) :=
  (lowerMixedSpan ell hl).map (restriction3 ell (p * ell) (dvd_mul_left ell p)) ⊔
    classSeriesSpan (p * ell) hM

theorem trace_upperGood {p ell : ℕ} (hl : 0 < ell) (hM : 0 < p * ell) {f : Weight (p * ell) 3}
    (hf : f ∈ upperGood p ell hl hM) :
    normalizedTrace3 ell (p * ell) hM f ∈ target p ell hl hM := by
  obtain ⟨g, hg, h, hh, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  obtain ⟨g0, hg0, rfl⟩ := Submodule.mem_map.mp hg
  rw [normalizedTrace3_restriction]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hg0)
    (Submodule.mem_sup_right (Submodule.mem_map_of_mem hh))

/-- A mixed form at `p`-divisible labels is a restricted lower mixed form. -/
theorem cross_mem_upper {p ell : ℕ} (hp : 0 < p) (hl : 0 < ell) (hM : 0 < p * ell)
    {u v u' v' : ℤ} (hu : (p : ℤ) ∣ u) (hv : (p : ℤ) ∣ v) (hu' : (p : ℤ) ∣ u') (hv' : (p : ℤ) ∣ v') :
    crossForm (p * ell) hM u v u' v' ∈ upperGood p ell hl hM := by
  obtain ⟨k1, rfl⟩ := hu
  obtain ⟨k2, rfl⟩ := hv
  obtain ⟨k3, rfl⟩ := hu'
  obtain ⟨k4, rfl⟩ := hv'
  have he : crossForm (p * ell) hM ((p : ℤ) * k1) ((p : ℤ) * k2) ((p : ℤ) * k3) ((p : ℤ) * k4) =
      restriction3 ell (p * ell) (dvd_mul_left ell p) (crossForm ell hl k1 k2 k3 k4) := by
    apply DFunLike.ext
    intro τ
    rw [restriction3_apply, crossForm_apply, crossForm_apply,
      TorsionMuDistributionNat.xValue_scale hp ell k1 k2 τ]
    unfold lambdaValue
    rw [TorsionCorrelation.reg_scale p ell hp hl k3 k4 τ]
  rw [he]
  exact Submodule.mem_sup_left (Submodule.mem_map_of_mem
    (Submodule.subset_span ⟨((k1, k2), (k3, k4)), rfl⟩))

theorem classSeries_le_upper {p ell : ℕ} (hl : 0 < ell) (hM : 0 < p * ell) :
    classSeriesSpan (p * ell) hM ≤ upperGood p ell hl hM := le_sup_right

/-! ### Case `P ≡ 0 (mod p)` -/

theorem trace_cross_first_zero (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (hpl : p ∣ ell)
    (a b c d : ℤ) (ha : (p : ℤ) ∣ a) (hb : (p : ℤ) ∣ b) :
    normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) a b c d) ∈
      target p ell hl (Nat.mul_pos (Fact.out : p.Prime).pos hl) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  set hM := Nat.mul_pos hp hl
  have : NeZero (p * ell) := ⟨hM.ne'⟩
  by_cases hcd : (c : ZMod p) ≠ 0 ∨ (d : ZMod p) ≠ 0
  · -- `Q` primitive: average over the complete fibre of `Q`
    have hmove : ∀ r t : ℤ, normalizedTrace3 ell (p * ell) hM
        (crossForm (p * ell) hM a b (c + ell * r) (d + ell * t)) =
        normalizedTrace3 ell (p * ell) hM (crossForm (p * ell) hM a b c d) := by
      intro r t
      obtain ⟨γ, hγ, h1, h2⟩ := exists_rank_one_move p ell hpl c d a b 0 hcd
        (by simpa using ha) (by simpa using hb) r t
      refine normalizedTrace3_cross_move ell (p * ell) hM (a, b) (c, d) (a, b)
        (c + ell * r, d + ell * t) γ hγ ?_ h1
      simpa using h2
    have havg : normalizedTrace3 ell (p * ell) hM (crossForm (p * ell) hM a b c d) =
        ((p : ℂ) ^ 2)⁻¹ • normalizedTrace3 ell (p * ell) hM
          (∑ r : Fin p, ∑ t : Fin p, crossForm (p * ell) hM a b
            (c + ell * ((r : ℕ) : ℤ)) (d + ell * ((t : ℕ) : ℤ))) := by
      have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
      rw [map_sum]
      simp_rw [map_sum, hmove]
      rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_smul,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        show ((p : ℂ) ^ 2)⁻¹ * ((p * p : ℕ) : ℂ) = 1 by push_cast; field_simp, one_smul]
    have hfib : (∑ r : Fin p, ∑ t : Fin p, crossForm (p * ell) hM a b
        (c + ell * ((r : ℕ) : ℤ)) (d + ell * ((t : ℕ) : ℤ))) =
        (p : ℂ) • crossForm (p * ell) hM a b ((p : ℤ) * c) ((p : ℤ) * d) := by
      apply DFunLike.ext
      intro τ
      simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul, crossForm_apply]
      simp_rw [← Finset.mul_sum]
      rw [lam_sum hp hl c d τ]
      unfold lambdaValue
      rw [TorsionCorrelation.reg_scale p ell hp hl c d τ]
      ring
    rw [havg, hfib, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (trace_upperGood hl hM
      (cross_mem_upper hp hl hM ha hb (dvd_mul_right _ _) (dvd_mul_right _ _))))
  · push Not at hcd
    have hc : (p : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp hcd.1
    have hd : (p : ℤ) ∣ d := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hcd.2
    exact trace_upperGood hl hM (cross_mem_upper hp hl hM ha hb hc hd)

/-! ### Case `P` primitive, `Q ≡ σ P` with `σ ∈ {0, 1, -1}` -/

/-- The paired fibre sum of mixed forms at slope `σ`. -/
def fibre3 (p ell : ℕ) (hM : 0 < p * ell) (a b c d σ : ℤ) : Weight (p * ell) 3 :=
  ∑ r : Fin p, ∑ t : Fin p, crossForm (p * ell) hM (a + ell * ((r : ℕ) : ℤ))
    (b + ell * ((t : ℕ) : ℤ)) (c + ell * (σ * ((r : ℕ) : ℤ))) (d + ell * (σ * ((t : ℕ) : ℤ)))

theorem trace_fibre3_average (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (hpl : p ∣ ell)
    (a b c d σ : ℤ) (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0)
    (hc : (p : ℤ) ∣ c - σ * a) (hd : (p : ℤ) ∣ d - σ * b) :
    normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) a b c d) =
      ((p : ℂ) ^ 2)⁻¹ • normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (fibre3 p ell (Nat.mul_pos (Fact.out : p.Prime).pos hl) a b c d σ) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  set hM := Nat.mul_pos hp hl
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hmove : ∀ r t : ℤ, normalizedTrace3 ell (p * ell) hM
      (crossForm (p * ell) hM (a + ell * r) (b + ell * t) (c + ell * (σ * r)) (d + ell * (σ * t))) =
      normalizedTrace3 ell (p * ell) hM (crossForm (p * ell) hM a b c d) := by
    intro r t
    obtain ⟨γ, hγ, h1, h2⟩ := exists_rank_one_move p ell hpl a b c d σ hab hc hd r t
    exact normalizedTrace3_cross_move ell (p * ell) hM (a, b) (c, d) (a + ell * r, b + ell * t)
      (c + ell * (σ * r), d + ell * (σ * t)) γ hγ h1 h2
  unfold fibre3
  rw [map_sum]
  simp_rw [map_sum, hmove]
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_smul,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    show ((p : ℂ) ^ 2)⁻¹ * ((p * p : ℕ) : ℂ) = 1 by push_cast; field_simp, one_smul]

theorem fibre3_zero_mem (p ell : ℕ) (hp : 0 < p) (hl : 0 < ell) (hM : 0 < p * ell)
    (a b c d : ℤ) (hc : (p : ℤ) ∣ c) (hd : (p : ℤ) ∣ d) :
    fibre3 p ell hM a b c d 0 ∈ upperGood p ell hl hM := by
  have he : fibre3 p ell hM a b c d 0 =
      ((p : ℂ) ^ 2) • crossForm (p * ell) hM ((p : ℤ) * a) ((p : ℤ) * b) c d := by
    apply DFunLike.ext
    intro τ
    unfold fibre3
    simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul, crossForm_apply, zero_mul,
      mul_zero, add_zero]
    simp_rw [← Finset.sum_mul]
    rw [WeierstrassDistributionNat.x_distribution_nat p ell hp hl τ a b,
      TorsionMuDistributionNat.xValue_scale hp ell a b τ]
    ring
  rw [he]
  exact Submodule.smul_mem _ _ (cross_mem_upper hp hl hM (dvd_mul_right _ _) (dvd_mul_right _ _) hc hd)

/-- The combination of lower terms in the second distribution congruence. -/
theorem combo_mem (p ell : ℕ) (hp : 0 < p) (hl : 0 < ell) (hM : 0 < p * ell) (a b c d : ℤ)
    (hac : (p : ℤ) ∣ a + c) (hbd : (p : ℤ) ∣ b + d) :
    (-(p : ℂ) • xlamForm (p * ell) hM ((p : ℤ) * a) ((p : ℤ) * b) +
        ((p : ℂ) ^ 2) • crossForm (p * ell) hM ((p : ℤ) * a) ((p : ℤ) * b) (a + c) (b + d) +
        (p : ℂ) • crossForm (p * ell) hM (a + c) (b + d) ((p : ℤ) * a) ((p : ℤ) * b) +
        (p : ℂ) • crossForm (p * ell) hM (a + c) (b + d) ((p : ℤ) * c) ((p : ℤ) * d) -
        ((p : ℂ) ^ 2) • xlamForm (p * ell) hM (a + c) (b + d)) ∈ upperGood p ell hl hM := by
  have dpa : (p : ℤ) ∣ (p : ℤ) * a := dvd_mul_right _ _
  have dpb : (p : ℤ) ∣ (p : ℤ) * b := dvd_mul_right _ _
  have dpc : (p : ℤ) ∣ (p : ℤ) * c := dvd_mul_right _ _
  have dpd : (p : ℤ) ∣ (p : ℤ) * d := dvd_mul_right _ _
  refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_))
    (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_)
  · exact cross_mem_upper hp hl hM dpa dpb dpa dpb
  · exact cross_mem_upper hp hl hM dpa dpb hac hbd
  · exact cross_mem_upper hp hl hM hac hbd dpa dpb
  · exact cross_mem_upper hp hl hM hac hbd dpc dpd
  · exact cross_mem_upper hp hl hM hac hbd hac hbd

theorem fibre3_neg_one_mem (p ell : ℕ) (hp : 0 < p) (hl : 0 < ell) (hM : 0 < p * ell)
    (a b c d : ℤ) (hac : (p : ℤ) ∣ a + c) (hbd : (p : ℤ) ∣ b + d) :
    fibre3 p ell hM a b c d (-1) ∈ upperGood p ell hl hM := by
  have hrel := cross_distribution_mem p ell hp hl a b c d
  have he : fibre3 p ell hM a b c d (-1) = ∑ r : Fin p, ∑ s : Fin p,
      crossForm (p * ell) (Nat.mul_pos hp hl) (a + ell * ((r : ℕ) : ℤ)) (b + ell * ((s : ℕ) : ℤ))
        (c - ell * ((r : ℕ) : ℤ)) (d - ell * ((s : ℕ) : ℤ)) := by
    unfold fibre3
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    congr 1 <;> ring
  rw [he]
  have hsplit := Submodule.add_mem (upperGood p ell hl hM)
    (classSeries_le_upper hl hM hrel) (combo_mem p ell hp hl hM a b c d hac hbd)
  rwa [sub_add_cancel] at hsplit

theorem fibre3_one_mem (p ell : ℕ) (hp : 0 < p) (hl : 0 < ell) (hM : 0 < p * ell)
    (a b c d : ℤ) (hac : (p : ℤ) ∣ a - c) (hbd : (p : ℤ) ∣ b - d) :
    fibre3 p ell hM a b c d 1 ∈ upperGood p ell hl hM := by
  have he : fibre3 p ell hM a b c d 1 = -fibre3 p ell hM a b (-c) (-d) (-1) := by
    unfold fibre3
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← crossForm_neg_right]
    congr 1 <;> ring
  rw [he]
  exact Submodule.neg_mem _ (fibre3_neg_one_mem p ell hp hl hM a b (-c) (-d)
    (by simpa [sub_eq_add_neg] using hac) (by simpa [sub_eq_add_neg] using hbd))

/-- **Slopes `0, 1, -1`.** -/
theorem trace_cross_slope_small (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (hpl : p ∣ ell)
    (a b c d σ : ℤ) (hσ : σ = 0 ∨ σ = 1 ∨ σ = -1)
    (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0)
    (hc : (p : ℤ) ∣ c - σ * a) (hd : (p : ℤ) ∣ d - σ * b) :
    normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) a b c d) ∈
      target p ell hl (Nat.mul_pos (Fact.out : p.Prime).pos hl) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  set hM := Nat.mul_pos hp hl
  rw [trace_fibre3_average p ell hl hpl a b c d σ hab hc hd]
  apply Submodule.smul_mem
  apply trace_upperGood hl hM
  rcases hσ with rfl | rfl | rfl
  · exact fibre3_zero_mem p ell hp hl hM a b c d (by simpa using hc) (by simpa using hd)
  · exact fibre3_one_mem p ell hp hl hM a b c d
      (by rw [show a - c = -(c - 1 * a) by ring]; exact (dvd_neg).mpr hc)
      (by rw [show b - d = -(d - 1 * b) by ring]; exact (dvd_neg).mpr hd)
  · exact fibre3_neg_one_mem p ell hp hl hM a b c d
      (by rw [show a + c = c - (-1) * a by ring]; exact hc)
      (by rw [show b + d = d - (-1) * b by ring]; exact hd)

/-! ### Independent pairs -/

/-- The one-parameter line sum of mixed forms. -/
theorem lambda_line_fourier (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (a b c d : ℤ) (τ : ℍ) :
    (∑ γ : Fin p, lambdaValue (p * ell) (c + ell * (((γ : ℕ) : ℤ) * a))
        (d + ell * (((γ : ℕ) : ℤ) * b)) τ) =
      ∑ a' : Fin (p * ell), ∑ b' : Fin (p * ell),
        (if (p : ℤ) ∣ ((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b then
          -((p : ℂ) / ((p * ell : ℕ) : ℂ)) *
            TorsionFourierComparison.character (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) c d *
              lambdaValue (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) τ
        else 0) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hM : 0 < p * ell := Nat.mul_pos hp hl
  have : NeZero p := ⟨hp.ne'⟩
  have : NeZero ell := ⟨hl.ne'⟩
  have : NeZero (p * ell) := ⟨hM.ne'⟩
  have hterm : ∀ γ : Fin p, lambdaValue (p * ell) (c + ell * (((γ : ℕ) : ℤ) * a))
      (d + ell * (((γ : ℕ) : ℤ) * b)) τ =
      TorsionWeierstrassData.scale * (-(1 / ((p * ell : ℕ) : ℂ)) *
        ∑ a' : Fin (p * ell), ∑ b' : Fin (p * ell),
          TorsionDistributionTwo.reg (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) τ *
            (TorsionFourierComparison.character (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) c d *
              Torsion.w p (((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b) ^ (γ : ℕ))) := by
    intro γ
    unfold lambdaValue
    rw [TorsionFourierComparison.torsion_fourier_duality (p * ell) τ]
    congr 2
    refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
    congr 1
    change TorsionFourierComparison.character (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ)
      (c + ell * (((γ : ℕ) : ℤ) * a)) (d + ell * (((γ : ℕ) : ℤ) * b)) = _
    rw [character_line_shift, character_line]
  simp_rw [hterm]
  have hgeom : ∀ a' b' : Fin (p * ell), (∑ γ : Fin p,
      Torsion.w p (((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b) ^ (γ : ℕ)) =
      if (p : ℤ) ∣ ((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b then (p : ℂ) else 0 := by
    intro a' b'
    rw [TorsionFourierComparison.finite_geometric p _ (TorsionFourierComparison.w_pow_level p _)]
    simp only [AllLevelTorsionCoefficients.w_eq_one_iff p]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  have hsum : (∑ γ : Fin p, TorsionWeierstrassData.scale * (-(1 / ((p * ell : ℕ) : ℂ)) *
      (TorsionDistributionTwo.reg (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) τ *
        (TorsionFourierComparison.character (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) c d *
          Torsion.w p (((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b) ^ (γ : ℕ))))) =
      TorsionWeierstrassData.scale * (-(1 / ((p * ell : ℕ) : ℂ)) *
        (TorsionDistributionTwo.reg (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) τ *
          (TorsionFourierComparison.character (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) c d *
            ∑ γ : Fin p, Torsion.w p (((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b) ^ (γ : ℕ)))) := by
    simp_rw [Finset.mul_sum]
  rw [hsum, hgeom]
  unfold lambdaValue
  split_ifs
  · ring
  · ring

/-- **Independent pairs reduce to dependent pairs.** -/
theorem trace_cross_independent (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (hpl : p ∣ ell)
    (a b c d : ℤ) (hΔ : ((a * d - b * c : ℤ) : ZMod p) ≠ 0)
    (hdep : ∀ a' b' : ℤ, (p : ℤ) ∣ a * b' - b * a' →
      normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
          (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) a b a' b') ∈
        target p ell hl (Nat.mul_pos (Fact.out : p.Prime).pos hl)) :
    normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) a b c d) ∈
      target p ell hl (Nat.mul_pos (Fact.out : p.Prime).pos hl) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  set hM := Nat.mul_pos hp hl
  have : NeZero (p * ell) := ⟨hM.ne'⟩
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hmove : ∀ γ : ℤ, normalizedTrace3 ell (p * ell) hM
      (crossForm (p * ell) hM a b (c + ell * (γ * a)) (d + ell * (γ * b))) =
      normalizedTrace3 ell (p * ell) hM (crossForm (p * ell) hM a b c d) := by
    intro γ
    obtain ⟨g, hg, h1, h2⟩ := exists_rank_two_move p ell hpl a b c d hΔ γ
    exact normalizedTrace3_cross_move ell (p * ell) hM (a, b) (c, d) (a, b)
      (c + ell * (γ * a), d + ell * (γ * b)) g hg h1 h2
  have havg : normalizedTrace3 ell (p * ell) hM (crossForm (p * ell) hM a b c d) =
      ((p : ℂ))⁻¹ • normalizedTrace3 ell (p * ell) hM
        (∑ γ : Fin p, crossForm (p * ell) hM a b (c + ell * (((γ : ℕ) : ℤ) * a))
          (d + ell * (((γ : ℕ) : ℤ) * b))) := by
    rw [map_sum]
    simp_rw [hmove]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hp0, one_smul]
  have hline : (∑ γ : Fin p, crossForm (p * ell) hM a b (c + ell * (((γ : ℕ) : ℤ) * a))
      (d + ell * (((γ : ℕ) : ℤ) * b))) =
      ∑ a' : Fin (p * ell), ∑ b' : Fin (p * ell),
        (if (p : ℤ) ∣ ((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b then
          (-((p : ℂ) / ((p * ell : ℕ) : ℂ)) *
            TorsionFourierComparison.character (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) c d) •
            crossForm (p * ell) hM a b ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ)
        else 0) := by
    apply DFunLike.ext
    intro τ
    simp only [_root_.sum_apply, crossForm_apply]
    simp_rw [← Finset.mul_sum]
    rw [lambda_line_fourier p ell hl a b c d τ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    split_ifs
    · rw [_root_.smul_apply, smul_eq_mul, crossForm_apply]
      ring
    · rw [mul_zero]
      rfl
  rw [havg, hline, map_sum]
  apply Submodule.smul_mem
  refine Submodule.sum_mem _ fun a' _ => ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun b' _ => ?_
  split_ifs with hdiv
  · rw [map_smul]
    apply Submodule.smul_mem
    apply hdep
    rw [show a * ((b' : ℕ) : ℤ) - b * ((a' : ℕ) : ℤ) = ((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b by ring]
    exact hdiv
  · rw [map_zero]; exact Submodule.zero_mem _

/-! ### Assembly -/

/-- The slope-`σ` statement for primitive first labels. -/
def SlopeClosed (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (σ : ℤ) : Prop :=
  ∀ a b c d : ℤ, ((a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0) → (p : ℤ) ∣ c - σ * a →
    (p : ℤ) ∣ d - σ * b →
    normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) a b c d) ∈
      target p ell hl (Nat.mul_pos (Fact.out : p.Prime).pos hl)

theorem slopeClosed_small (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (hpl : p ∣ ell)
    (σ : ℤ) (hσ : σ = 0 ∨ σ = 1 ∨ σ = -1) : SlopeClosed p ell hl σ :=
  fun a b c d hab hc hd => trace_cross_slope_small p ell hl hpl a b c d σ hσ hab hc hd

/-- **All labels, given every slope.** -/
theorem trace_cross_mem_of_slopes (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (hpl : p ∣ ell)
    (hS : ∀ σ : ℤ, SlopeClosed p ell hl σ) (a b c d : ℤ) :
    normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) a b c d) ∈
      target p ell hl (Nat.mul_pos (Fact.out : p.Prime).pos hl) := by
  by_cases hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0
  · have hdepcase : ∀ a' b' : ℤ, (p : ℤ) ∣ a * b' - b * a' →
        normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
            (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) a b a' b') ∈
          target p ell hl (Nat.mul_pos (Fact.out : p.Prime).pos hl) := by
      intro a' b' hdet
      obtain ⟨σ, hc, hd⟩ := exists_slope p a b a' b' hab hdet
      exact hS σ a b a' b' hab hc hd
    by_cases hΔ : ((a * d - b * c : ℤ) : ZMod p) = 0
    · exact hdepcase c d ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hΔ)
    · exact trace_cross_independent p ell hl hpl a b c d hΔ hdepcase
  · push Not at hab
    exact trace_cross_first_zero p ell hl hpl a b c d
      ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hab.1)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hab.2)

/-- Every slope modulo `2` or `3` has a representative in `{0, 1, -1}`. -/
theorem slopeClosed_of_small_prime (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (hpl : p ∣ ell)
    (hp : p = 2 ∨ p = 3) (σ : ℤ) : SlopeClosed p ell hl σ := by
  intro a b c d hab hc hd
  have hrep : ∃ ρ : ℤ, (ρ = 0 ∨ ρ = 1 ∨ ρ = -1) ∧ (p : ℤ) ∣ σ - ρ := by
    rcases hp with rfl | rfl
    · have h0 := Int.emod_nonneg σ (by norm_num : (2 : ℤ) ≠ 0)
      have h1 := Int.emod_lt_of_pos σ (by norm_num : (0 : ℤ) < 2)
      have hq := Int.emod_add_mul_ediv σ 2
      interval_cases hr : σ % 2
      · exact ⟨0, Or.inl rfl, ⟨σ / 2, by push_cast; linarith⟩⟩
      · exact ⟨1, Or.inr (Or.inl rfl), ⟨σ / 2, by push_cast; linarith⟩⟩
    · have h0 := Int.emod_nonneg σ (by norm_num : (3 : ℤ) ≠ 0)
      have h1 := Int.emod_lt_of_pos σ (by norm_num : (0 : ℤ) < 3)
      have hq := Int.emod_add_mul_ediv σ 3
      interval_cases hr : σ % 3
      · exact ⟨0, Or.inl rfl, ⟨σ / 3, by push_cast; linarith⟩⟩
      · exact ⟨1, Or.inr (Or.inl rfl), ⟨σ / 3, by push_cast; linarith⟩⟩
      · exact ⟨-1, Or.inr (Or.inr rfl), ⟨σ / 3 + 1, by push_cast; linarith⟩⟩
  obtain ⟨ρ, hρ, hσρ⟩ := hrep
  refine slopeClosed_small p ell hl hpl ρ hρ a b c d hab ?_ ?_
  · rw [show c - ρ * a = (c - σ * a) + (σ - ρ) * a by ring]
    exact dvd_add hc (dvd_mul_of_dvd_left hσρ a)
  · rw [show d - ρ * b = (d - σ * b) + (σ - ρ) * b by ring]
    exact dvd_add hd (dvd_mul_of_dvd_left hσρ b)

/-- **Unconditional closure for `p = 2, 3`.** -/
theorem trace_cross_mem_small_prime (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (hpl : p ∣ ell)
    (hp : p = 2 ∨ p = 3) (a b c d : ℤ) :
    normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) a b c d) ∈
      target p ell hl (Nat.mul_pos (Fact.out : p.Prime).pos hl) :=
  trace_cross_mem_of_slopes p ell hl hpl (slopeClosed_of_small_prime p ell hl hpl hp) a b c d

end ZInQ.Contrib.HeckePrimeRationality.RepeatedPrimeMixedTrace
