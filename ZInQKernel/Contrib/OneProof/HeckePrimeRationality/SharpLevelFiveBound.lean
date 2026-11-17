import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.SturmBound
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Parity

/-!
# Sharp coefficient bound at level five

The product of the squares of a form and its diamond-two translate descends
from Γ₁(5) to Γ₀(5). Its weight is four times the original weight, while its
order at infinity is at least twice the original order. The index-six Sturm
bound for Γ₀(5) therefore gives truncation injectivity through the weight.
-/

noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace CoeffRational.SharpLevelFiveBound

/-- The residue class of two as a unit modulo five. -/
def two : (ZMod 5)ˣ := ZMod.unitOfCoprime 2 (by decide)

lemma two_mul_two : two * two = -1 := by
  apply Units.ext
  norm_num [two]
  decide +kernel

lemma unit_cases (u : (ZMod 5)ˣ) :
    u = 1 ∨ u = two ∨ u = -1 ∨ u = (-1) * two := by
  revert u
  decide +kernel

lemma sign_sq (k : ℤ) : ((-1 : ℂ) ^ k) ^ 2 = 1 := by
  rcases Int.even_or_odd k with hk | hk <;> simp [hk.neg_one_zpow]

lemma diamond_two_twice (k : ℤ)
    (f : ModularForm ((Gamma1 5).map (mapGL ℝ)) k) :
    diamondOp k two (diamondOp k two f) = ((-1 : ℂ) ^ k) • f := by
  rw [← LinearMap.comp_apply, ← diamondOp_mul, two_mul_two]
  exact TauCeti.diamondOp_neg_one k f

lemma diamond_two_ne_zero {k : ℤ}
    {f : ModularForm ((Gamma1 5).map (mapGL ℝ)) k} (hf : f ≠ 0) :
    diamondOp k two f ≠ 0 := by
  intro h
  have h' := congrArg (diamondOp k two⁻¹) h
  rw [map_zero] at h'
  have hleft : diamondOp k two⁻¹ (diamondOp k two f) = f := by
    rw [← LinearMap.comp_apply, ← diamondOp_mul, inv_mul_cancel,
      diamondOp_one, LinearMap.id_apply]
  exact hf (hleft ▸ h')

/-- The quartic product, initially at its original level. -/
def quarticGamma1 {k : ℤ}
    (f : ModularForm ((Gamma1 5).map (mapGL ℝ)) k) :
    ModularForm ((Gamma1 5).map (mapGL ℝ)) (4 * k) :=
  ModularForm.mcast (by ring)
    ((f.mul f).mul ((diamondOp k two f).mul (diamondOp k two f)))

lemma quarticGamma1_apply {k : ℤ}
    (f : ModularForm ((Gamma1 5).map (mapGL ℝ)) k) (z : ℍ) :
    quarticGamma1 f z = f z ^ 2 * diamondOp k two f z ^ 2 := by
  change (f z * f z) * (diamondOp k two f z * diamondOp k two f z) = _
  ring

lemma diamond_quartic_value {k : ℤ}
    (f : ModularForm ((Gamma1 5).map (mapGL ℝ)) k)
    (u : (ZMod 5)ˣ) (z : ℍ) :
    (diamondOp k u f z) ^ 2 * (diamondOp k u (diamondOp k two f) z) ^ 2 =
      f z ^ 2 * diamondOp k two f z ^ 2 := by
  rcases unit_cases u with rfl | rfl | rfl | rfl
  · simp
  · rw [diamond_two_twice]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [sign_sq]
    ring
  · rw [TauCeti.diamondOp_neg_one, TauCeti.diamondOp_neg_one]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [sign_sq]
    ring
  · simp only [diamondOp_mul, LinearMap.comp_apply,
      TauCeti.diamondOp_neg_one, diamond_two_twice, FunLike.coe_smul,
      Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [sign_sq]
    ring

lemma quartic_slash_Gamma0 {k : ℤ}
    (f : ModularForm ((Gamma1 5).map (mapGL ℝ)) k) (γ : ↥(Gamma0 5)) :
    (⇑(quarticGamma1 f)) ∣[4 * k] mapGL ℝ (γ : SL(2, ℤ)) =
      ⇑(quarticGamma1 f) := by
  let u := (Gamma0Map 5).toHomUnits γ
  have hf : (⇑f) ∣[k] (γ : SL(2, ℤ)) = ⇑(diamondOp k u f) :=
    (coe_diamondOp k u γ rfl f).symm
  have hg : (⇑(diamondOp k two f)) ∣[k] (γ : SL(2, ℤ)) =
      ⇑(diamondOp k u (diamondOp k two f)) :=
    (coe_diamondOp k u γ rfl (diamondOp k two f)).symm
  have he : ⇑(quarticGamma1 f) =
      (⇑f * ⇑f) * (⇑(diamondOp k two f) * ⇑(diamondOp k two f)) := by
    ext z
    rw [quarticGamma1_apply]
    simp [pow_two]
  change (⇑(quarticGamma1 f)) ∣[4 * k] (γ : SL(2, ℤ)) = ⇑(quarticGamma1 f)
  rw [he,
    show 4 * k = (k + k) + (k + k) by ring,
    ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2,
    ModularForm.mul_slash_SL2, hf, hg]
  ext z
  simpa only [Pi.mul_apply, ← pow_two, Pi.pow_apply] using diamond_quartic_value f u z

/-- The same analytic product is a holomorphic form on Γ₀(5). -/
def quartic {k : ℤ}
    (f : ModularForm ((Gamma1 5).map (mapGL ℝ)) k) :
    ModularForm ((Gamma0 5).map (mapGL ℝ)) (4 * k) where
  toFun := quarticGamma1 f
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact quartic_slash_Gamma0 f ⟨γ, hγ⟩
  holo' := (quarticGamma1 f).holo'
  bdd_at_cusps' {c} hc := by
    have hc' : IsCusp c ((Gamma1 5).map (mapGL ℝ)) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
      exact hc
    exact (quarticGamma1 f).bdd_at_cusps' hc'

lemma quartic_qExpansion {k : ℤ}
    (f : ModularForm ((Gamma1 5).map (mapGL ℝ)) k) :
    qExpansion 1 (quartic f) =
      (qExpansion 1 f) ^ 2 * (qExpansion 1 (diamondOp k two f)) ^ 2 := by
  change qExpansion 1
      ((f.mul f).mul ((diamondOp k two f).mul (diamondOp k two f))) = _
  rw [ModularForm.qExpansion_mul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map 5),
    ModularForm.qExpansion_mul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map 5),
    ModularForm.qExpansion_mul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map 5)]
  simp [pow_two]

lemma quartic_ne_zero {k : ℤ}
    {f : ModularForm ((Gamma1 5).map (mapGL ℝ)) k} (hf : f ≠ 0) :
    quartic f ≠ 0 := by
  have hp : qExpansion 1 f ≠ 0 := by
    intro h
    exact hf ((ModularForm.qExpansion_eq_zero_iff one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map 5) f).mp h)
  have hq : qExpansion 1 (diamondOp k two f) ≠ 0 := by
    intro h
    exact diamond_two_ne_zero hf ((ModularForm.qExpansion_eq_zero_iff one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map 5) (diamondOp k two f)).mp h)
  intro h
  have hzero : qExpansion 1 (quartic f) = 0 :=
    (ModularForm.qExpansion_eq_zero_iff one_pos
      (TauCeti.one_mem_strictPeriods_Gamma0_map 5) _).mpr h
  rw [quartic_qExpansion] at hzero
  exact mul_ne_zero (pow_ne_zero 2 hp) (pow_ne_zero 2 hq) hzero

/-- Vanishing through the weight forces a level-five analytic modular form to vanish. -/
theorem eq_zero_of_coeff_eq_zero (k : ℤ) (hk : 0 ≤ k)
    (f : ModularForm ((Gamma1 5).map (mapGL ℝ)) k)
    (hcoeff : ∀ n : ℕ, n ≤ k.toNat → (qExpansion 1 f).coeff n = 0) : f = 0 := by
  have hp : (↑(k.toNat + 1) : ℕ∞) ≤ (qExpansion 1 f).order :=
    PowerSeries.nat_le_order _ _ (fun n hn ↦ hcoeff n (by omega))
  have horder : (↑(2 * (k.toNat + 1)) : ℕ∞) ≤ (qExpansion 1 (quartic f)).order := by
    rw [quartic_qExpansion, pow_two, pow_two,
      PowerSeries.order_mul, PowerSeries.order_mul, PowerSeries.order_mul]
    calc
      (↑(2 * (k.toNat + 1)) : ℕ∞) =
          (↑(k.toNat + 1) : ℕ∞) + (↑(k.toNat + 1) : ℕ∞) := by
        norm_cast
        omega
      _ ≤ (qExpansion 1 f).order + (qExpansion 1 f).order := add_le_add hp hp
      _ ≤ ((qExpansion 1 f).order + (qExpansion 1 f).order) +
          ((qExpansion 1 (diamondOp k two f)).order +
            (qExpansion 1 (diamondOp k two f)).order) := le_self_add
  have hindex : (Gamma0 5).index = 6 := by
    simpa using Gamma0_prime_index 5 (by decide)
  have harith : ((4 * k * 6).toNat / 12) = 2 * k.toNat := by omega
  have hzero : quartic f = 0 := by
    apply TauCeti.ModularForm.sturm_bound_finiteIndex_SL2Z
    rw [hindex, CongruenceSubgroup.strictWidthInfty_Gamma0]
    simp only [Nat.cast_ofNat]
    rw [harith]
    exact lt_of_lt_of_le (by exact_mod_cast (show 2 * k.toNat < 2 * (k.toNat + 1) by omega))
      horder
  by_contra hf
  exact quartic_ne_zero hf hzero

end CoeffRational.SharpLevelFiveBound
