import ZInQKernel.Contrib.OneProof.TYZLemma29Mod2
import ZInQKernel.Contrib.OneProof.T21Proof.BrandtValue
import ZInQKernel.Contrib.OneProof.T21Proof.LUnit

/-!
# `TYZThm21At31` proved (task t21-proof)

`ZInQ.Contrib.TYZDecomp.H29Split.TYZThm21At31` (TYZ Theorem 2.1 at `n = 3`, `(d₁, d₂) = (3, 1)`) with no
hypotheses:
* `Cl(ℚ(√−3)) = 1` (`pid_three`), so the class sum is `f_3(1)` (`tv_eq_of_toClassGroup_eq`);
* `f_3(1) = ±3` for every admissible `τ` and every test vector `f_3` (`T21Proof.testVector_one`, a Brandt
  computation at `n = 3`: `T21Proof/BrandtValue.lean`);
* `#μ(ℚ(√−3)) = 6` (Mathlib's `IsCyclotomicExtension.Rat.torsionOrder_eq`), so `w_K = 3`;
* `0 < ‖𝓛(m)²‖ < 4` at `m = 1, 3` (rigorous bounds on `L(C_1, 1)` and `L(C_3, 1)` from Hecke's continuation,
  `T21Proof/LUnit.lean`, with `decide +kernel` certificates), and `ℓ(m)² = 𝓛(m)²` with `ℓ(m) ∈ ℤ`, so
  `ℓ(1), ℓ(3) = ±1`.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp
open ZInQ.Contrib.TYZDecomp.H29Split NumberField NumberField.Units IsDedekindDomain
open scoped Quaternion

/-! ## `#μ(ℚ(√−3)) = 6` -/

theorem torsionOrder_three : torsionOrder (QNeg 3) = 6 := by
  have := ZInQ.Contrib.TYZLcal.isCyclotomicExtension_three
  rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 3)]
  decide

/-! ## The class sum collapses -/

instance subsingleton_cl3 : Subsingleton (ClassGroup (𝓞 (QNeg 3))) := by
  have h1 : Fintype.card (ClassGroup (𝓞 (QNeg 3))) = 1 :=
    card_classGroup_eq_one_iff.mpr ZInQ.Contrib.TYZLcal.pid_three
  exact Fintype.card_le_one_iff_subsingleton.mp h1.le

theorem classSum_eq {τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]} {f : ℍ[AQ] → ℤ} (hf : InPiZ 3 τ f) :
    ∑ t : ClassGroup (𝓞 (QNeg 3)), f ((tauHatU 3 τ (clLift 3 t) : ℍ[AQ]ˣ) : ℍ[AQ]) = f 1 := by
  rw [Fintype.sum_subsingleton _ 1]
  have h : FiniteAdeleRing.toClassGroup (𝓞 (QNeg 3)) (QNeg 3) (clLift 3 1) =
      FiniteAdeleRing.toClassGroup (𝓞 (QNeg 3)) (QNeg 3) 1 := Subsingleton.elim _ _
  rw [tv_eq_of_toClassGroup_eq hf h, map_one, Units.val_one]

/-! ## `ℓ(m) = ±1` -/

theorem int_eq_pm_one_of_sq {a : ℤ} {z : ℂ} (ha : (a : ℂ) ^ 2 = z) (h0 : 0 < ‖z‖) (h4 : ‖z‖ < 4) :
    a = 1 ∨ a = -1 := by
  have hn : ‖z‖ = ((a ^ 2 : ℤ) : ℝ) := by
    rw [← ha, norm_pow, Complex.norm_intCast]; push_cast; rw [sq_abs]
  rw [hn] at h0 h4
  have h0' : 0 < a ^ 2 := by exact_mod_cast h0
  have h4' : a ^ 2 < 4 := by exact_mod_cast h4
  have : a ≠ 0 := by rintro rfl; simp at h0'
  have h2 : -2 < a ∧ a < 2 := by constructor <;> nlinarith
  omega

/-! ## `0 < ‖𝓛(m)²‖ < 4` at `m = 1, 3` -/

theorem omegaInt_pos : 0 < omegaInt := by
  have := ZInQ.Contrib.TYZLcal.omegaInt_ge_two; linarith

theorem lcalSq_one_bounds : 0 < ‖lcalSq 1‖ ∧ ‖lcalSq 1‖ < 4 := by
  obtain ⟨hre, hle⟩ := lValOne_one_bounds
  have hω := ZInQ.Contrib.TYZLcal.omegaInt_ge_two
  have hpos : 0 < ‖lValOne 1‖ := lt_of_lt_of_le (by norm_num) (hre.trans (Complex.re_le_norm _))
  have hn : ‖lcalSq 1‖ = ‖lValOne 1‖ / (omegaInt / 4) := by
    rw [ZInQ.Contrib.TYZLcal.lcalSq_one, norm_div, norm_div, Complex.norm_real,
      Real.norm_of_nonneg omegaInt_pos.le, show ‖(4 : ℂ)‖ = 4 by norm_num]
  rw [hn]
  constructor
  · exact div_pos hpos (by linarith)
  · rw [div_lt_iff₀ (by linarith)]; linarith

theorem lcalSq_three_bounds : 0 < ‖lcalSq 3‖ ∧ ‖lcalSq 3‖ < 4 := by
  obtain ⟨hre, hle⟩ := lValOne_three_bounds
  have hω := ZInQ.Contrib.TYZLcal.omegaInt_ge_two
  have hpos : 0 < ‖lValOne 3‖ := lt_of_lt_of_le (by norm_num) (hre.trans (Complex.re_le_norm _))
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt 3 < 1.75 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hden : (2 : ℂ) ^ ((2 * ((Nat.primeFactors 3).card : ℤ)) - 3) * ((omegaTYZ 3 : ℝ) : ℂ) =
      ((omegaInt / Real.sqrt 3 : ℝ) : ℂ) := by
    rw [Nat.Prime.primeFactors Nat.prime_three, Finset.card_singleton, omegaTYZ]
    push_cast
    field_simp
  have hn : ‖lcalSq 3‖ = ‖lValOne 3‖ / (omegaInt / Real.sqrt 3) := by
    rw [lcalSq, hden, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hn]
  have hq : 0 < omegaInt / Real.sqrt 3 := div_pos omegaInt_pos hs0
  constructor
  · exact div_pos hpos hq
  · rw [div_lt_iff₀ hq, mul_div_assoc', lt_div_iff₀ hs0]
    have := mul_le_mul hle hs.le hs0.le (by norm_num)
    linarith

/-! ## The theorem -/

/-- **`TYZThm21At31` proved** (TYZ Theorem 2.1 at `n = 3`, `(d₁, d₂) = (3, 1)`), with no hypotheses. -/
theorem tyzThm21At31 : TYZThm21At31 := by
  intro τ hτ f hf ℓ hℓ
  have h1 := int_eq_pm_one_of_sq (hℓ 1 squarefree_one (Or.inl rfl)) lcalSq_one_bounds.1
    lcalSq_one_bounds.2
  have h3 := int_eq_pm_one_of_sq (hℓ 3 Nat.prime_three.squarefree (Or.inr rfl))
    lcalSq_three_bounds.1 lcalSq_three_bounds.2
  rw [classSum_eq hf.1, torsionOrder_three]
  have hp : ℓ 3 * ℓ 1 = 1 ∨ ℓ 3 * ℓ 1 = -1 := by
    rcases h1 with h1 | h1 <;> rcases h3 with h3 | h3 <;> simp [h1, h3]
  rcases testVector_one hτ hf with hf1 | hf1 <;> rcases hp with hp | hp
  · exact ⟨1, Or.inl rfl, by rw [hf1, hp]; norm_num⟩
  · exact ⟨-1, Or.inr rfl, by rw [hf1, hp]; norm_num⟩
  · exact ⟨-1, Or.inr rfl, by rw [hf1, hp]; norm_num⟩
  · exact ⟨1, Or.inl rfl, by rw [hf1, hp]; norm_num⟩

end ZInQ.Contrib.T21Proof
