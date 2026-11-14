import ZInQKernel.Contrib.TYZDecomp.Leaves
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

/-!
# tyz-lcal: `TYZLcalOne` from the two other L-leaves and an analytic bound

Report: `docs/research/tyz-lcal.md`; log `scratch/tyz-lcal/log.md`.

The leaves `TYZThm11Integral`, `TYZLcalOne`, `TYZLemma29Mod2` are those of
`ZInQKernel/Contrib/TYZDecomp/Leaves.lean` (imported, not copied, so that the theorems below are
about exactly those Props).

* `gCl_three : gCl 3 = 1` — `ℚ(√−3)` has class number one (`ℚ(√−3) = ℚ(ζ₃)`, Mathlib's
  `IsCyclotomicExtension.Rat.three_pid`).
* `ell_one_odd`: under `TYZThm11Integral` and `TYZLemma29Mod2`, every integer square root of
  `lcalSq 1` is odd (Lemma 2.9 at `m = 3`: `𝓛(3)𝓛(1) ≡ g(3) = 1`).
* `lcalOne_of_leaves`: `TYZThm11Integral → TYZLemma29Mod2 → LValOneBound → TYZLcalOne`, where
  `LValOneBound : ‖L(C₁, 1)‖ < (9/4) ∫₁^∞ dx/√(x³ − x)` is glue (a numerical estimate; true value
  `L(C₁,1) = ¼ ∫₁^∞ dx/√(x³−x) ≈ 0.6555`).
-/

noncomputable section

namespace ZInQ.Contrib.TYZLcal

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp

/-! ## `g(3) = 1` -/

/-- The primitive cube root of unity `(−1 + √−3)/2` in `ℚ(√−3)`. -/
def zeta3 : QNeg 3 := ⟨-1 / 2, 1 / 2⟩

theorem zeta3_pow_three : zeta3 ^ 3 = 1 := by
  ext <;> simp [zeta3, pow_succ, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> norm_num

theorem zeta3_isPrimitiveRoot : IsPrimitiveRoot zeta3 3 := by
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) zeta3_pow_three fun l hl hl3 => ?_
  interval_cases l
  · intro h
    have := congrArg QuadraticAlgebra.im h
    simp [zeta3, QuadraticAlgebra.im_one] at this
  · intro h
    have := congrArg QuadraticAlgebra.im h
    simp [zeta3, pow_succ, QuadraticAlgebra.im_one] at this
    norm_num at this

instance isCyclotomicExtension_three : IsCyclotomicExtension {3} ℚ (QNeg 3) := by
  rw [IsCyclotomicExtension.iff_singleton]
  refine ⟨⟨zeta3, zeta3_isPrimitiveRoot⟩, fun x => ?_⟩
  have hz : zeta3 ∈ Algebra.adjoin ℚ {b : QNeg 3 | b ^ 3 = 1} :=
    Algebra.subset_adjoin zeta3_pow_three
  have hx : x = algebraMap ℚ (QNeg 3) (x.re + x.im) + (2 * x.im) • zeta3 := by
    ext <;> simp [zeta3] <;> ring
  rw [hx]
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.smul_mem _ hz _)

theorem pid_three : IsPrincipalIdealRing (NumberField.RingOfIntegers (QNeg 3)) :=
  IsCyclotomicExtension.Rat.three_pid (QNeg 3)

/-- **`g(3) = #2Cl(ℚ(√−3)) = 1`.** -/
theorem gCl_three : gCl 3 = 1 := by
  have h1 : Fintype.card (ClassGroup (NumberField.RingOfIntegers (QNeg 3))) = 1 :=
    card_classGroup_eq_one_iff.mpr pid_three
  have : Subsingleton (ClassGroup (NumberField.RingOfIntegers (QNeg 3))) :=
    Fintype.card_le_one_iff_subsingleton.mp h1.le
  unfold gCl
  exact Nat.card_unique

theorem gNat_three : gNat 3 = 1 := by
  simp only [gNat, show (3 : ℕ) ≠ 0 by norm_num, dite_false]
  exact gCl_three

/-! ## `𝓛(1)` is odd -/

/-- The value of `lcalSq` at `1`: `lcalSq 1 = 4 L(C₁, 1) / ∫₁^∞ dx/√(x³−x)`. -/
theorem lcalSq_one : lcalSq 1 = lValOne 1 / ((omegaInt : ℂ) / 4) := by
  unfold lcalSq omegaTYZ
  congr 1
  simp only [Nat.primeFactors_one, Finset.card_empty, Nat.cast_zero, mul_zero, zero_sub,
    Nat.cast_one, Real.sqrt_one, div_one]
  push_cast
  rw [zpow_neg, zpow_ofNat]
  ring

open Classical in
/-- A sign choice of `𝓛` on the classes `1, 3` from integrality alone. -/
def ellOf (h11 : TYZThm11Integral) : ℕ → ℤ := fun m =>
  if hm : Squarefree m ∧ (m % 8 = 1 ∨ m % 8 = 3) then (h11 m hm.1 hm.2).choose else 0

theorem ellOf_sq (h11 : TYZThm11Integral) :
    ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ellOf h11 m : ℂ)) ^ 2 = lcalSq m := by
  intro m hsq hcl
  have hm : Squarefree m ∧ (m % 8 = 1 ∨ m % 8 = 3) := ⟨hsq, hcl⟩
  simp only [ellOf, hm]
  exact (h11 m hsq hcl).choose_spec

theorem divisors_three_filter : (Nat.divisors 3).filter (fun d => d % 8 = 1) = {1} := by decide

/-- Lemma 2.9 at `m = 3` makes `ℓ(3)ℓ(1)` odd. -/
theorem ell_three_mul_ell_one_odd (h29 : TYZLemma29Mod2) {ℓ : ℕ → ℤ}
    (hℓ : ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m) :
    ((ℓ 3 * ℓ 1 : ℤ) : ZMod 2) = 1 := by
  have h := (h29 ℓ hℓ).2 3 Nat.prime_three.squarefree (by norm_num)
  rw [divisors_three_filter, Finset.sum_singleton, gNat_three] at h
  simpa using h

/-- **Every integer square root of `lcalSq 1` is odd** (given the two TYZ leaves). -/
theorem ell_one_odd (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) {a : ℤ}
    (ha : (a : ℂ) ^ 2 = lcalSq 1) : Odd a := by
  have h := ell_three_mul_ell_one_odd h29 (ellOf_sq h11)
  have h1 : ((ellOf h11 1 : ℂ)) ^ 2 = lcalSq 1 := ellOf_sq h11 1 squarefree_one (Or.inl rfl)
  have hsq : ellOf h11 1 ^ 2 = a ^ 2 := by exact_mod_cast h1.trans ha.symm
  have hodd1 : Odd (ellOf h11 1) := by
    rw [Int.cast_mul] at h
    have : ((ellOf h11 1 : ℤ) : ZMod 2) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h; exact zero_ne_one h
    rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    exact Int.not_even_iff_odd.mp fun he => this (even_iff_two_dvd.mp he)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq.symm with h | h
  · rw [h]; exact hodd1
  · rw [h]; exact hodd1.neg

/-! ## The analytic bound and the reduction -/

/-- **Glue (numerical estimate)**: `‖L(C₁, 1)‖ < (9/4) ∫₁^∞ dx/√(x³ − x)`, with `L(C₁, 1)` the value
at `1` of the continuation of Mathlib's `L(y² = x³ − x, s)`. True value: `L(C₁,1) ≈ 0.6555`,
`∫ ≈ 2.6221` (`scratch/tyz-lcal/out_lcal_check.txt`). Not a leaf: it is an estimate of an explicit
Mellin integral (`Contrib/HeckeFE`). -/
def LValOneBound : Prop := ‖lValOne 1‖ < 9 / 4 * omegaInt

/-- **`TYZLcalOne` from the two other L-leaves and the bound.** If `lcalSq 1 = a²` with `a` odd
(`ell_one_odd`) and `a² ≠ 1`, then `a² ≥ 9` and `‖L(C₁,1)‖ = a² ω/4 ≥ 9ω/4`. -/
theorem lcalOne_of_leaves (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hB : LValOneBound) :
    TYZLcalOne := by
  obtain ⟨a, ha⟩ := h11 1 squarefree_one (Or.inl rfl)
  have hodd := ell_one_odd h11 h29 ha
  have hω : (0 : ℝ) < omegaInt := omegaInt_pos
  have hval : lValOne 1 = ((a ^ 2 : ℤ) : ℂ) * ((omegaInt : ℂ) / 4) := by
    have hne : (omegaInt : ℂ) / 4 ≠ 0 := by
      exact div_ne_zero (Complex.ofReal_ne_zero.mpr hω.ne') (by norm_num)
    rw [lcalSq_one] at ha
    push_cast
    rw [ha, div_mul_cancel₀ _ hne]
  have hnorm : ‖lValOne 1‖ = (a ^ 2 : ℝ) * (omegaInt / 4) := by
    rw [hval, norm_mul, Complex.norm_div, Complex.norm_real, Real.norm_of_nonneg hω.le]
    push_cast
    rw [Complex.norm_pow, Complex.norm_intCast, sq_abs]
    norm_num
  have ha1 : a ^ 2 = 1 := by
    by_contra hne
    obtain ⟨k, rfl⟩ := hodd
    have h9 : (9 : ℤ) ≤ (2 * k + 1) ^ 2 := by
      have : k ≠ 0 ∧ k ≠ -1 := by
        constructor <;> rintro rfl <;> simp at hne
      rcases lt_trichotomy k 0 with hk | hk | hk
      · have : k ≤ -2 := by omega
        nlinarith
      · exact absurd hk this.1
      · nlinarith
    have h9' : (9 : ℝ) ≤ ((2 * k + 1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast h9
    have : 9 / 4 * omegaInt ≤ ‖lValOne 1‖ := by
      rw [hnorm]; nlinarith
    exact absurd hB (not_lt.mpr this)
  have : lcalSq 1 = ((a : ℂ)) ^ 2 := ha.symm
  rw [TYZLcalOne, this]
  exact_mod_cast ha1

end ZInQ.Contrib.TYZLcal
