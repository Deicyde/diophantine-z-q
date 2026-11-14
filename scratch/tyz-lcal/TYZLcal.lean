import ZInQKernel.Contrib.TYZDecomp.Leaves
import ZInQKernel.Contrib.HeckeAll.Continuation
import ZInQKernel.Contrib.GaussFE.FunctionalEquation5
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
* Part 2 (`LBound`): `lValOneBound : LValOneBound`, proved. `L(C₁, s)` is continued by the explicit
  Hecke theta integral of `Contrib/HeckeFE` (`isLContinuation_Fone`), `Λ_{a,b}(1)` is split at `1`
  and the integrals over `(1, ∞)` are bounded with explicit majorants of Mathlib's Hurwitz kernels
  (`norm_lValOne_one_le : ‖L(C₁,1)‖ ≤ 3.35`); and `omegaInt_ge_two : 2 ≤ ∫₁^∞ dx/√(x³−x)`.
* **`tyzLcalOne_of_leaves : TYZThm11Integral → TYZLemma29Mod2 → TYZLcalOne`**: the leaf
  `TYZLcalOne` is a consequence of the two other L-leaves (Lemma 2.9 at `m = 3` only).
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


open Complex Real Set MeasureTheory HurwitzZeta ZInQ.Contrib.HeckeFE



/-! ## §1. `Λ(1)` as two integrals over `(1, ∞)` -/

theorem integrableOn_gaussTheta (a b : UnitAddCircle) : IntegrableOn (gaussTheta a b) (Ioi 0) := by
  have h := mellinConvergent_gaussTheta a b 1
  simpa [MellinConvergent] using h

/-- `Λ_{a,b}(1) = ∫₁^∞ θ_{a,b} + ∫₁^∞ θ^dual_{a,b}` (split at `1`, substitute `x ↦ 1/x` on `(0, 1)`). -/
theorem gaussLambda_one_eq (a b : UnitAddCircle) :
    gaussLambda a b 1 = (∫ x in Ioi 1, gaussTheta a b x) + ∫ x in Ioi 1, gaussThetaDual a b x := by
  have hint := integrableOn_gaussTheta a b
  have h1 : gaussLambda a b 1 = ∫ x in Ioi 0, gaussTheta a b x := by
    simp [gaussLambda, mellin]
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ici 1) := by
    rw [Set.disjoint_iff]; rintro x ⟨⟨-, hx⟩, hx'⟩; exact absurd hx' (not_le.mpr hx)
  rw [h1, ← Ioo_union_Ici_eq_Ioi zero_lt_one,
    setIntegral_union hdisj measurableSet_Ici (hint.mono_set Ioo_subset_Ioi_self)
      (hint.mono_set (Ici_subset_Ioi.mpr zero_lt_one)),
    integral_Ici_eq_integral_Ioi, add_comm]
  congr 1
  -- the substitution
  set f : ℝ → ℂ := (Ioo (0 : ℝ) 1).indicator (gaussTheta a b) with hf
  have e1 : ∫ x in Ioo 0 1, gaussTheta a b x = mellin f 1 := by
    simp only [mellin, sub_self, cpow_zero, one_smul, hf]
    rw [setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Ioo_subset_Ioi_self]
  have e2 : mellin f 1 = mellin (fun t => f t⁻¹) (-1) := by
    rw [← mellin_comp_inv]; simp
  rw [e1, e2, mellin]
  have e3 : ∫ x in Ioi (1 : ℝ), gaussThetaDual a b x =
      ∫ x in Ioi (0 : ℝ), (Ioi (1 : ℝ)).indicator (gaussThetaDual a b) x := by
    rw [setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.mpr
      (Ioi_subset_Ioi zero_le_one)]
  rw [e3]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [hf]
  by_cases h1t : 1 < t
  · have hmem : t⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.mpr ht, inv_lt_one_of_one_lt₀ h1t⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show t ∈ Ioi (1:ℝ) from h1t),
      ← one_div, gaussTheta_one_div a b ht, smul_eq_mul, ← mul_assoc]
    have : (t : ℂ) ^ ((-1 : ℂ) - 1) * ((t ^ (2 : ℝ) : ℝ) : ℂ) = 1 := by
      rw [show (-1 : ℂ) - 1 = -((2 : ℝ) : ℂ) by norm_num, cpow_neg,
        ← ofReal_cpow ht.le, inv_mul_cancel₀]
      exact ofReal_ne_zero.mpr (rpow_pos_of_pos ht _).ne'
    rw [this, one_mul]
  · have hmem : t⁻¹ ∉ Ioo (0 : ℝ) 1 := fun h => h1t ((inv_lt_one₀ ht).mp h.2)
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show t ∉ Ioi (1:ℝ) from h1t),
      smul_zero]

/-! ## §2. Integrals of exponentially decaying functions over `(1, ∞)` -/

theorem integral_exp_decay {C c : ℝ} (hc : 0 < c) :
    ∫ x in Ioi (1 : ℝ), C * Real.exp (-c * (x - 1)) = C / c := by
  have h : ∀ x : ℝ, C * Real.exp (-c * (x - 1)) = (C * Real.exp c) * Real.exp (-c * x) := by
    intro x; rw [mul_assoc, ← Real.exp_add]; ring_nf
  simp_rw [h]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -c < 0)]
  rw [mul_one, neg_div_neg_eq, mul_div_assoc', mul_assoc, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, mul_one]

theorem integrableOn_exp_decay (C : ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => C * Real.exp (-c * (x - 1))) (Ioi 1) := by
  have h : ∀ x : ℝ, C * Real.exp (-c * (x - 1)) = (C * Real.exp c) * Real.exp (-c * x) := by
    intro x; rw [mul_assoc, ← Real.exp_add]; ring_nf
  simp_rw [h]
  exact (integrableOn_exp_mul_Ioi (by linarith : -c < 0) 1).const_mul _

/-- If `‖f x‖ ≤ C e^{−c(x−1)}` on `(1, ∞)` then `‖∫₁^∞ f‖ ≤ C/c`. -/
theorem norm_integral_Ioi_one_le {f : ℝ → ℂ} {C c : ℝ} (hc : 0 < c)
    (hf : ∀ x : ℝ, 1 < x → ‖f x‖ ≤ C * Real.exp (-c * (x - 1))) :
    ‖∫ x in Ioi (1 : ℝ), f x‖ ≤ C / c := by
  rw [← integral_exp_decay (C := C) hc]
  refine norm_integral_le_of_norm_le (integrableOn_exp_decay C hc) ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => hf x hx)


/-! ## §3. The explicit continuation of `L(C₁, s)` and its value at `1` -/

/-- `π^s Γ(s)⁻¹ Λ_{a,b}(s)` is the lattice series for `Re s > 3/2` (proof of
`HeckeFE.gaussL_continuation`). -/
theorem gaussL_eq_of_re (a b : ℝ) {s : ℂ} (hs : 3 / 2 < s.re) :
    (π : ℂ) ^ s * (Gamma s)⁻¹ * gaussLambda a b s = gaussL a b s := by
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hpi : (π : ℂ) ^ s ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero
    (by rintro rfl; norm_num at hs)).mpr (ofReal_ne_zero.mpr pi_ne_zero)
  rw [← (hasSum_gaussLambda a b hs).tsum_eq, gaussL]
  simp_rw [mul_div_assoc]
  rw [tsum_mul_left, cpow_neg]
  field_simp

/-- The explicit continuation of a twisted lattice series (the function of
`HeckeFE.twistedL_continuation`). -/
def Fexp (M : ℕ) (c : ZMod M × ZMod M → ℂ) (s : ℂ) : ℂ :=
  ∑ j : Fin M × Fin M, c (((j.1 : ℤ) : ZMod M), ((j.2 : ℤ) : ZMod M)) *
    ((M : ℂ) / (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ s) *
      ((π : ℂ) ^ s * (Gamma s)⁻¹ *
        gaussLambda (((j.1 : ℝ) / M : ℝ) : UnitAddCircle) (((j.2 : ℝ) / M : ℝ) : UnitAddCircle) s)

theorem differentiable_Fexp (M : ℕ) [NeZero M] (c : ZMod M × ZMod M → ℂ) :
    Differentiable ℂ (Fexp M c) := by
  have hM : (((M : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne M))
  have : NeZero (((M : ℝ) ^ 2 : ℝ) : ℂ) := ⟨hM⟩
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  have : NeZero (π : ℂ) := ⟨hpi⟩
  unfold Fexp
  refine Differentiable.fun_sum fun j _ => ?_
  refine (Differentiable.const_mul ?_ _).mul ?_
  · simp_rw [div_eq_mul_inv, ← cpow_neg]
    exact (differentiable_const_cpow_of_neZero _).comp differentiable_id.neg |>.const_mul _
  · exact ((differentiable_const_cpow_of_neZero (π : ℂ)).mul differentiable_one_div_Gamma).mul
      (differentiable_gaussLambda _ _)

theorem Fexp_eq_twistedL (M : ℕ) [NeZero M] (c : ZMod M × ZMod M → ℂ) {s : ℂ}
    (hs : 3 / 2 < s.re) : Fexp M c s = twistedL M c s := by
  rw [twistedL_eq M c hs, Fexp]
  exact Finset.sum_congr rfl fun j _ => by rw [gaussL_eq_of_re _ _ hs]

/-- The coefficient function of `L(C₁, s)` on `ℤ[i]/4`: `¼ · unitOf`. -/
def cU (x : ZMod 4 × ZMod 4) : ℂ := (1 / 4) * unitOf x

/-- `F₁ := Fexp 4 cU` is the entire continuation of Mathlib's `L(y² = x³ − x, s)`. -/
theorem isLContinuation_Fone : ZInQ.Literature.IsLContinuation (ZInQ.Contrib.TYZDecomp.curveC 1)
    (Fexp 4 cU) := by
  refine ⟨differentiable_Fexp 4 cU, fun s hs => ?_⟩
  have hD1 : DeuringCd 1 := deuringCd_of_gaussPointCount (by norm_num) squarefree_one
    ZInQ.Contrib.GaussFE.gaussPointCount
  rw [Fexp_eq_twistedL 4 cU hs, ZInQ.Contrib.TYZDecomp.curveC,
    ZInQ.Literature.LSeries_cd_eq (by norm_num) squarefree_one s]
  refine (LSeries_eq_twistedL 4 cU _ (fun n hn => ?_) hs).symm
  rw [hD1 n hn, heckeCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [cU, jacobiSym.one_right, Int.cast_one, one_mul]
  ring

/-- **`L(C₁, 1)` as a finite combination of the `Λ_{a,b}(1)`.** -/
theorem lValOne_one_eq : ZInQ.Contrib.TYZDecomp.lValOne 1 =
    ∑ j : Fin 4 × Fin 4, cU (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4)) * (1 / 4) *
      ((π : ℂ) * gaussLambda (((j.1 : ℝ) / 4 : ℝ) : UnitAddCircle) (((j.2 : ℝ) / 4 : ℝ) : UnitAddCircle) 1) := by
  rw [ZInQ.Contrib.TYZDecomp.lValOne_eq isLContinuation_Fone, Fexp]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [cpow_one, Complex.Gamma_one, inv_one, mul_one]
  push_cast
  norm_num

/-! ## §4. Numerical bounds for `exp` -/

theorem exp_neg_le_of {y c : ℝ} (hc : 0 < c) (h : c ≤ Real.exp y) : Real.exp (-y) ≤ 1 / c := by
  rw [Real.exp_neg, inv_eq_one_div]; exact one_div_le_one_div_of_le hc h

theorem exp_nat_ge (k : ℕ) : (2.718 : ℝ) ^ k ≤ Real.exp k := by
  have h1 := Real.exp_one_gt_d9
  have : Real.exp (k : ℝ) = Real.exp 1 ^ k := by rw [← Real.exp_nat_mul]; ring_nf
  rw [this]
  exact pow_le_pow_left₀ (by norm_num) (by linarith) k

theorem exp_quad_ge {y : ℝ} (hy : 0 ≤ y) : 1 + y + y ^ 2 / 2 ≤ Real.exp y :=
  Real.quadratic_le_exp_of_nonneg hy

theorem pi_gt' : (3.14 : ℝ) < π := Real.pi_gt_d2
theorem pi_lt' : π < (3.15 : ℝ) := Real.pi_lt_d2

/-- `e^{−π} ≤ 1/20`. -/
theorem exp_neg_pi_le : Real.exp (-π) ≤ 1 / 20 := by
  have h := exp_nat_ge 3
  have : Real.exp 3 ≤ Real.exp π := Real.exp_le_exp.mpr (by linarith [pi_gt'])
  refine exp_neg_le_of (by norm_num) ?_
  push_cast at h; nlinarith

/-- `e^{−π/4} ≤ 0.48`. -/
theorem exp_neg_pi_div_four_le : Real.exp (-(π / 4)) ≤ 0.48 := by
  have hp := pi_gt'
  have h := exp_quad_ge (y := π / 4) (by positivity)
  have : (0.48 : ℝ) = 1 / (1 / 0.48) := by norm_num
  rw [this]; refine exp_neg_le_of (by norm_num) ?_
  nlinarith

/-- `e^{−π/16} ≤ 0.83`. -/
theorem exp_neg_pi_div_sixteen_le : Real.exp (-(π / 16)) ≤ 0.83 := by
  have hp := pi_gt'
  have h := exp_quad_ge (y := π / 16) (by positivity)
  have : (0.83 : ℝ) = 1 / (1 / 0.83) := by norm_num
  rw [this]; refine exp_neg_le_of (by norm_num) ?_
  nlinarith

/-- `e^{−9π/16} ≤ 0.18`. -/
theorem exp_neg_nine_pi_div_sixteen_le : Real.exp (-(9 * π / 16)) ≤ 0.18 := by
  have hp := pi_gt'
  have h1 := exp_nat_ge 1
  have h := exp_quad_ge (y := 9 * π / 16 - 1) (by linarith)
  have hsplit : Real.exp (9 * π / 16) = Real.exp 1 * Real.exp (9 * π / 16 - 1) := by
    rw [← Real.exp_add]; ring_nf
  have : (0.18 : ℝ) = 1 / (1 / 0.18) := by norm_num
  rw [this]; refine exp_neg_le_of (by norm_num) ?_
  rw [hsplit]
  push_cast at h1
  have hu : (0.766 : ℝ) ≤ 9 * π / 16 - 1 := by linarith
  have h2 : (2.059 : ℝ) ≤ Real.exp (9 * π / 16 - 1) := by nlinarith
  nlinarith

/-- `e^{−3π/2} ≤ 1/50`. -/
theorem exp_neg_three_pi_div_two_le : Real.exp (-(3 * π / 2)) ≤ 1 / 50 := by
  have h := exp_nat_ge 4
  have : Real.exp 4 ≤ Real.exp (3 * π / 2) := Real.exp_le_exp.mpr (by linarith [pi_gt'])
  refine exp_neg_le_of (by norm_num) ?_
  push_cast at h; nlinarith

/-- `e^{−5π/2} ≤ 1/1000`. -/
theorem exp_neg_five_pi_div_two_le : Real.exp (-(5 * π / 2)) ≤ 1 / 1000 := by
  have h := exp_nat_ge 7
  have : Real.exp 7 ≤ Real.exp (5 * π / 2) := Real.exp_le_exp.mpr (by linarith [pi_gt'])
  refine exp_neg_le_of (by norm_num) ?_
  push_cast at h; nlinarith

/-! ## §5. Majorants for the Hurwitz kernels on `x ≥ 1` -/

theorem int_cases' (n : ℤ) : (∃ m : ℕ, n = m) ∨ ∃ m : ℕ, n = -((m : ℤ) + 1) := by
  rcases n with m | m
  · exact Or.inl ⟨m, rfl⟩
  · exact Or.inr ⟨m, Int.negSucc_eq m⟩

/-- A majorant on `ℤ` glued from two sequences on `ℕ`. -/
def zmaj (A B : ℕ → ℝ) (n : ℤ) : ℝ := if 0 ≤ n then A n.toNat else B (-n - 1).toNat

theorem zmaj_nat (A B : ℕ → ℝ) (m : ℕ) : zmaj A B m = A m := by simp [zmaj]

theorem zmaj_neg (A B : ℕ → ℝ) (m : ℕ) : zmaj A B (-((m : ℤ) + 1)) = B m := by
  have h : ¬ (0 : ℤ) ≤ -((m : ℤ) + 1) := by omega
  have h2 : (-(-((m : ℤ) + 1)) - 1).toNat = m := by omega
  simp only [zmaj, h, ite_false, h2]

theorem hasSum_zmaj {A B : ℕ → ℝ} {α β : ℝ} (hA : HasSum A α) (hB : HasSum B β) :
    HasSum (zmaj A B) (α + β) :=
  HasSum.of_nat_of_neg_add_one (by simpa only [zmaj_nat] using hA)
    (by simpa only [zmaj_neg] using hB)

theorem hasSum_lin_geom {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (c : ℝ) :
    HasSum (fun n : ℕ => ((n : ℝ) + c) * r ^ n) (r / (1 - r) ^ 2 + c * (1 - r)⁻¹) := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
    (by rwa [Real.norm_of_nonneg h0])).add ((hasSum_geometric_of_lt_one h0 h1).mul_left c)
  convert h using 1
  funext n; ring

theorem exp_pow_eq (y : ℝ) (m : ℕ) : Real.exp y ^ m = Real.exp (m * y) :=
  (Real.exp_nat_mul y m).symm

theorem nat_sq_ge (m : ℕ) : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
  have : m ≤ m ^ 2 := by nlinarith
  exact_mod_cast this

/-- **`|oddKernel(1/4)(x)| ≤ 0.37 e^{−π(x−1)/16}` for `x ≥ 1`.** -/
theorem abs_oddKernel_quarter_le {x : ℝ} (hx : 1 ≤ x) :
    |oddKernel ((1 / 4 : ℝ) : UnitAddCircle) x| ≤ 0.37 * Real.exp (-(π / 16) * (x - 1)) := by
  set E := Real.exp (-(π / 16) * (x - 1)) with hE
  set e1 := Real.exp (-(π / 16))
  set q := Real.exp (-(3 * π / 2))
  set e2 := Real.exp (-(9 * π / 16))
  set q2 := Real.exp (-(5 * π / 2))
  have hq : q ≤ 1 / 50 := exp_neg_three_pi_div_two_le
  have hq2 : q2 ≤ 1 / 1000 := exp_neg_five_pi_div_two_le
  have he1 : e1 ≤ 0.83 := exp_neg_pi_div_sixteen_le
  have he2 : e2 ≤ 0.18 := exp_neg_nine_pi_div_sixteen_le
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq20 : 0 ≤ q2 := (Real.exp_pos _).le
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have he10 : 0 ≤ e1 := (Real.exp_pos _).le
  have he20 : 0 ≤ e2 := (Real.exp_pos _).le
  set A : ℕ → ℝ := fun m => E * e1 * (((m : ℝ) + 1 / 4) * q ^ m)
  set B : ℕ → ℝ := fun m => E * e2 * (((m : ℝ) + 3 / 4) * q2 ^ m)
  have hA := (hasSum_lin_geom hq0 (by linarith) (1 / 4)).mul_left (E * e1)
  have hB := (hasSum_lin_geom hq20 (by linarith) (3 / 4)).mul_left (E * e2)
  have hpi := Real.pi_pos
  have key := HasSum.norm_le_of_bounded (hasSum_int_oddKernel (1 / 4) (by linarith : 0 < x))
    (hasSum_zmaj hA hB) (fun n => ?_)
  · rw [Real.norm_eq_abs] at key
    refine key.trans ?_
    -- numerics
    have h1 : q / (1 - q) ^ 2 + 1 / 4 * (1 - q)⁻¹ ≤ 0.276 := by
      have hpos : 0 < 1 - q := by linarith
      rw [← div_eq_mul_inv, div_add_div _ _ (by positivity) hpos.ne', div_le_iff₀ (by positivity)]
      nlinarith
    have h2 : q2 / (1 - q2) ^ 2 + 3 / 4 * (1 - q2)⁻¹ ≤ 0.753 := by
      have hpos : 0 < 1 - q2 := by linarith
      rw [← div_eq_mul_inv, div_add_div _ _ (by positivity) hpos.ne', div_le_iff₀ (by positivity)]
      nlinarith
    have h1' : 0 ≤ q / (1 - q) ^ 2 + 1 / 4 * (1 - q)⁻¹ := by
      have hpos : 0 < 1 - q := by linarith
      positivity
    have h2' : 0 ≤ q2 / (1 - q2) ^ 2 + 3 / 4 * (1 - q2)⁻¹ := by
      have hpos : 0 < 1 - q2 := by linarith
      positivity
    have : e1 * (q / (1 - q) ^ 2 + 1 / 4 * (1 - q)⁻¹) +
        e2 * (q2 / (1 - q2) ^ 2 + 3 / 4 * (1 - q2)⁻¹) ≤ 0.37 := by nlinarith
    nlinarith
  · rcases int_cases' n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [zmaj_nat]
      simp only [Int.cast_natCast]
      have hm := nat_sq_ge m
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ m + 1 / 4),
        abs_of_nonneg (Real.exp_pos _).le]
      have hexp : Real.exp (-π * ((m : ℝ) + 1 / 4) ^ 2 * x) ≤ E * e1 * q ^ m := by
        rw [exp_pow_eq, hE, ← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have : 0 ≤ ((m : ℝ) ^ 2 + m / 2) * (x - 1) := by
          apply mul_nonneg <;> nlinarith
        nlinarith
      calc ((m : ℝ) + 1 / 4) * Real.exp (-π * ((m : ℝ) + 1 / 4) ^ 2 * x)
          ≤ ((m : ℝ) + 1 / 4) * (E * e1 * q ^ m) := by gcongr
        _ = E * e1 * (((m : ℝ) + 1 / 4) * q ^ m) := by ring
    · rw [zmaj_neg]
      push_cast
      have hm := nat_sq_ge m
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hsq : (-((m : ℝ) + 1) + 1 / 4) ^ 2 = ((m : ℝ) + 3 / 4) ^ 2 := by ring
      rw [hsq, Real.norm_eq_abs, abs_mul, show -((m : ℝ) + 1) + 1 / 4 = -((m : ℝ) + 3 / 4) by ring,
        abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ m + 3 / 4),
        abs_of_nonneg (Real.exp_pos _).le]
      have hexp : Real.exp (-π * ((m : ℝ) + 3 / 4) ^ 2 * x) ≤ E * e2 * q2 ^ m := by
        rw [exp_pow_eq, hE, ← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have : 0 ≤ ((m : ℝ) ^ 2 + 3 * m / 2 + 1 / 2) * (x - 1) := by
          apply mul_nonneg <;> nlinarith
        nlinarith
      calc ((m : ℝ) + 3 / 4) * Real.exp (-π * ((m : ℝ) + 3 / 4) ^ 2 * x)
          ≤ ((m : ℝ) + 3 / 4) * (E * e2 * q2 ^ m) := by gcongr
        _ = E * e2 * (((m : ℝ) + 3 / 4) * q2 ^ m) := by ring

/-- The majorant `Σ_n e^{−π n² x} ≤ 21/19` (`x ≥ 1`), termwise. -/
theorem gauss_term_le {x : ℝ} (hx : 1 ≤ x) (n : ℤ) :
    Real.exp (-π * (n : ℝ) ^ 2 * x) ≤
      zmaj (fun m => Real.exp (-π) ^ m) (fun m => Real.exp (-π) * Real.exp (-π) ^ m) n := by
  have hpi := Real.pi_pos
  rcases int_cases' n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [zmaj_nat, exp_pow_eq]
    simp only [Int.cast_natCast]
    refine Real.exp_le_exp.mpr ?_
    have hm := nat_sq_ge m
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : 0 ≤ (m : ℝ) ^ 2 * (x - 1) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  · rw [zmaj_neg, exp_pow_eq, ← Real.exp_add]
    push_cast
    refine Real.exp_le_exp.mpr ?_
    have hm := nat_sq_ge m
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : 0 ≤ ((m : ℝ) + 1) ^ 2 * (x - 1) := mul_nonneg (by positivity) (by linarith)
    nlinarith

theorem hasSum_gauss_maj :
    HasSum (zmaj (fun m => Real.exp (-π) ^ m) (fun m => Real.exp (-π) * Real.exp (-π) ^ m))
      ((1 - Real.exp (-π))⁻¹ + Real.exp (-π) * (1 - Real.exp (-π))⁻¹) := by
  have hr := exp_neg_pi_le
  have h0 : 0 ≤ Real.exp (-π) := (Real.exp_pos _).le
  exact hasSum_zmaj (hasSum_geometric_of_lt_one h0 (by linarith))
    ((hasSum_geometric_of_lt_one h0 (by linarith)).mul_left _)

theorem gauss_maj_le : (1 - Real.exp (-π))⁻¹ + Real.exp (-π) * (1 - Real.exp (-π))⁻¹ ≤ 1.11 := by
  have hr := exp_neg_pi_le
  have h0 : 0 ≤ Real.exp (-π) := (Real.exp_pos _).le
  have hpos : 0 < 1 - Real.exp (-π) := by linarith
  rw [← one_add_mul, ← div_eq_mul_inv, div_le_iff₀ hpos]
  nlinarith

/-- **`|evenKernel 0 x| ≤ 1.11`** for `x ≥ 1`. -/
theorem abs_evenKernel_zero_le {x : ℝ} (hx : 1 ≤ x) :
    |evenKernel ((0 : ℝ) : UnitAddCircle) x| ≤ 1.11 := by
  have key := HasSum.norm_le_of_bounded (hasSum_int_evenKernel 0 (by linarith : 0 < x))
    hasSum_gauss_maj (fun n => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, add_zero]; exact gauss_term_le hx n)
  rw [Real.norm_eq_abs] at key
  exact key.trans gauss_maj_le

/-- **`|cosKernel b x| ≤ 1.11`** for `x ≥ 1`. -/
theorem abs_cosKernel_le (b : ℝ) {x : ℝ} (hx : 1 ≤ x) : |cosKernel (b : UnitAddCircle) x| ≤ 1.11 := by
  have key := HasSum.norm_le_of_bounded (hasSum_int_cosKernel b (by linarith : 0 < x))
    hasSum_gauss_maj (fun n => by
      rw [norm_mul, show (2 * π * I * b * n : ℂ) = 2 * π * I * ((b * n : ℝ) : ℂ) by push_cast; ring,
        norm_cexp_two_pi_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact gauss_term_le hx n)
  rw [Complex.norm_real, Real.norm_eq_abs] at key
  exact key.trans gauss_maj_le

/-- **`|evenKernel (1/2) x| ≤ 1.11`** for `x ≥ 1`. -/
theorem abs_evenKernel_half_le {x : ℝ} (hx : 1 ≤ x) :
    |evenKernel ((1 / 2 : ℝ) : UnitAddCircle) x| ≤ 1.11 := by
  have hr := exp_neg_pi_le
  have h4 := exp_neg_pi_div_four_le
  have h0 : 0 ≤ Real.exp (-π) := (Real.exp_pos _).le
  have h40 : 0 ≤ Real.exp (-(π / 4)) := (Real.exp_pos _).le
  have hpi := Real.pi_pos
  set A : ℕ → ℝ := fun m => Real.exp (-(π / 4)) * Real.exp (-π) ^ m
  have hA := (hasSum_geometric_of_lt_one h0 (by linarith)).mul_left (Real.exp (-(π / 4)))
  have key := HasSum.norm_le_of_bounded (hasSum_int_evenKernel (1 / 2) (by linarith : 0 < x))
    (hasSum_zmaj hA hA) (fun n => ?_)
  · rw [Real.norm_eq_abs] at key
    refine key.trans ?_
    have hpos : 0 < 1 - Real.exp (-π) := by linarith
    rw [← mul_add, ← two_mul, ← div_eq_mul_inv, mul_div_assoc', div_le_iff₀ hpos]
    nlinarith
  · rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    rcases int_cases' n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [zmaj_nat]
      simp only [Int.cast_natCast]
      rw [exp_pow_eq, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hm := nat_sq_ge m
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have : 0 ≤ ((m : ℝ) + 1 / 2) ^ 2 * (x - 1) := mul_nonneg (by positivity) (by linarith)
      nlinarith
    · rw [zmaj_neg]
      push_cast
      rw [exp_pow_eq, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hm := nat_sq_ge m
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have : 0 ≤ ((m : ℝ) + 1 / 2) ^ 2 * (x - 1) := mul_nonneg (by positivity) (by linarith)
      nlinarith

/-- **`|sinKernel a x| ≤ 0.112 e^{−π(x−1)}`** for `x ≥ 1`. -/
theorem abs_sinKernel_le (a : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    |sinKernel (a : UnitAddCircle) x| ≤ 0.112 * Real.exp (-π * (x - 1)) := by
  set E := Real.exp (-π * (x - 1)) with hE
  set r := Real.exp (-π)
  have hr : r ≤ 1 / 20 := exp_neg_pi_le
  have h0 : 0 ≤ r := (Real.exp_pos _).le
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hpi := Real.pi_pos
  set A : ℕ → ℝ := fun m => E * ((m : ℝ) * r ^ m)
  set B : ℕ → ℝ := fun m => E * r * (((m : ℝ) + 1) * r ^ m)
  have hA := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
    (by rw [Real.norm_of_nonneg h0]; linarith)).mul_left E
  have hB := (hasSum_lin_geom h0 (by linarith) 1).mul_left (E * r)
  have key := HasSum.norm_le_of_bounded (hasSum_int_sinKernel a (by linarith : 0 < x))
    (hasSum_zmaj hA hB) (fun n => ?_)
  · rw [Complex.norm_real, Real.norm_eq_abs] at key
    refine key.trans ?_
    have hpos : 0 < 1 - r := by linarith
    have hS : r / (1 - r) ^ 2 + r * (r / (1 - r) ^ 2 + 1 * (1 - r)⁻¹) = 2 * r / (1 - r) ^ 2 := by
      field_simp; ring
    have hS2 : 2 * r / (1 - r) ^ 2 ≤ 0.112 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    calc E * (r / (1 - r) ^ 2) + E * r * (r / (1 - r) ^ 2 + 1 * (1 - r)⁻¹)
        = E * (r / (1 - r) ^ 2 + r * (r / (1 - r) ^ 2 + 1 * (1 - r)⁻¹)) := by ring
      _ ≤ E * 0.112 := by rw [hS]; exact mul_le_mul_of_nonneg_left hS2 hE0
      _ = 0.112 * E := by ring
  · have hnorm : ‖-I * (n : ℂ) * cexp (2 * π * I * a * n) * Real.exp (-π * (n : ℝ) ^ 2 * x)‖ =
        |(n : ℝ)| * Real.exp (-π * (n : ℝ) ^ 2 * x) := by
      rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
        show (2 * π * I * a * n : ℂ) = 2 * π * I * ((a * n : ℝ) : ℂ) by push_cast; ring,
        norm_cexp_two_pi_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    rcases int_cases' n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [zmaj_nat]
      simp only [Int.cast_natCast]
      have hm := nat_sq_ge m
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      rw [abs_of_nonneg hm0]
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h
      have hexp : Real.exp (-π * (m : ℝ) ^ 2 * x) ≤ E * r ^ m := by
        rw [exp_pow_eq, hE, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have : 0 ≤ ((m : ℝ) ^ 2 - 1) * (x - 1) := mul_nonneg (by nlinarith) (by linarith)
        nlinarith
      calc (m : ℝ) * Real.exp (-π * (m : ℝ) ^ 2 * x) ≤ (m : ℝ) * (E * r ^ m) := by gcongr
        _ = E * ((m : ℝ) * r ^ m) := by ring
    · rw [zmaj_neg]
      push_cast
      have hm := nat_sq_ge m
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ m + 1)]
      have hexp : Real.exp (-π * (-((m : ℝ) + 1)) ^ 2 * x) ≤ E * r * r ^ m := by
        rw [exp_pow_eq, hE, ← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have : 0 ≤ (((m : ℝ) + 1) ^ 2 - 1) * (x - 1) := mul_nonneg (by nlinarith) (by linarith)
        nlinarith
      calc ((m : ℝ) + 1) * Real.exp (-π * (-((m : ℝ) + 1)) ^ 2 * x)
          ≤ ((m : ℝ) + 1) * (E * r * r ^ m) := by gcongr
        _ = E * r * (((m : ℝ) + 1) * r ^ m) := by ring

/-! ## §6. The bound for `Λ_{a,b}(1)` on the eight classes with `unitOf ≠ 0` -/

theorem neg_half_circle : -((1 / 2 : ℝ) : UnitAddCircle) = ((1 / 2 : ℝ) : UnitAddCircle) := by
  rw [← AddCircle.coe_neg]
  exact (QuotientAddGroup.eq).mpr (AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by norm_num⟩)

theorem neg_zero_circle : -((0 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := by simp

theorem three_quarter_circle : ((3 / 4 : ℝ) : UnitAddCircle) = -((1 / 4 : ℝ) : UnitAddCircle) := by
  rw [← AddCircle.coe_neg]
  exact (QuotientAddGroup.eq).mpr (AddSubgroup.mem_zmultiples_iff.mpr ⟨-1, by norm_num⟩)

theorem oddKernel_eq_zero_of_neg {b : UnitAddCircle} (h : -b = b) (x : ℝ) : oddKernel b x = 0 := by
  have := oddKernel_neg b x; rw [h] at this; linarith

theorem sinKernel_eq_zero_of_neg {b : UnitAddCircle} (h : -b = b) (x : ℝ) : sinKernel b x = 0 := by
  have := sinKernel_neg b x; rw [h] at this; linarith

/-- The two odd shifts `1/4`, `3/4`. -/
theorem abs_oddKernel_le {a : ℝ} (ha : a = 1 / 4 ∨ a = 3 / 4) {x : ℝ} (hx : 1 ≤ x) :
    |oddKernel (a : UnitAddCircle) x| ≤ 0.37 * Real.exp (-(π / 16) * (x - 1)) := by
  rcases ha with rfl | rfl
  · exact abs_oddKernel_quarter_le hx
  · rw [three_quarter_circle, oddKernel_neg, abs_neg]; exact abs_oddKernel_quarter_le hx

/-- The two even shifts `0`, `1/2`. -/
theorem abs_evenKernel_le {b : ℝ} (hb : b = 0 ∨ b = 1 / 2) {x : ℝ} (hx : 1 ≤ x) :
    |evenKernel (b : UnitAddCircle) x| ≤ 1.11 := by
  rcases hb with rfl | rfl
  · exact abs_evenKernel_zero_le hx
  · exact abs_evenKernel_half_le hx

theorem neg_eq_of_even {b : ℝ} (hb : b = 0 ∨ b = 1 / 2) :
    -(b : UnitAddCircle) = (b : UnitAddCircle) := by
  rcases hb with rfl | rfl
  · exact neg_zero_circle
  · exact neg_half_circle

/-- **`‖Λ_{a,b}(1)‖ ≤ 6.7/π`, odd `a`, even `b`.** -/
theorem norm_gaussLambda_le_A {a b : ℝ} (ha : a = 1 / 4 ∨ a = 3 / 4) (hb : b = 0 ∨ b = 1 / 2) :
    ‖gaussLambda (a : UnitAddCircle) (b : UnitAddCircle) 1‖ ≤ 6.7 / π := by
  have hpi := Real.pi_pos
  have hpi' := pi_gt'
  have hneg := neg_eq_of_even hb
  have h1 : ‖∫ x in Ioi (1 : ℝ), gaussTheta (a : UnitAddCircle) (b : UnitAddCircle) x‖ ≤
      (0.37 * 1.11) / (π / 16) := by
    refine norm_integral_Ioi_one_le (by positivity) fun x hx => ?_
    rw [gaussTheta, oddKernel_eq_zero_of_neg hneg, ofReal_zero, mul_zero, mul_zero, add_zero,
      norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have e1 := abs_oddKernel_le ha hx.le
    have e2 := abs_evenKernel_le hb hx.le
    have e0 : 0 ≤ Real.exp (-(π / 16) * (x - 1)) := (Real.exp_pos _).le
    calc |oddKernel (a : UnitAddCircle) x| * |evenKernel (b : UnitAddCircle) x|
        ≤ (0.37 * Real.exp (-(π / 16) * (x - 1))) * 1.11 :=
          mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
      _ = 0.37 * 1.11 * Real.exp (-(π / 16) * (x - 1)) := by ring
  have h2 : ‖∫ x in Ioi (1 : ℝ), gaussThetaDual (a : UnitAddCircle) (b : UnitAddCircle) x‖ ≤
      (0.112 * 1.11) / π := by
    refine norm_integral_Ioi_one_le hpi fun x hx => ?_
    rw [gaussThetaDual, sinKernel_eq_zero_of_neg hneg, ofReal_zero, mul_zero, mul_zero, add_zero,
      norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have e1 := abs_sinKernel_le a hx.le
    have e2 := abs_cosKernel_le b hx.le
    have e0 : 0 ≤ Real.exp (-π * (x - 1)) := (Real.exp_pos _).le
    calc |sinKernel (a : UnitAddCircle) x| * |cosKernel (b : UnitAddCircle) x|
        ≤ (0.112 * Real.exp (-π * (x - 1))) * 1.11 :=
          mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
      _ = 0.112 * 1.11 * Real.exp (-π * (x - 1)) := by ring
  rw [gaussLambda_one_eq]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 0.37 * 1.11 / (π / 16) + 0.112 * 1.11 / π := add_le_add h1 h2
    _ = (0.37 * 1.11 * 16 + 0.112 * 1.11) / π := by field_simp
    _ ≤ 6.7 / π := by rw [div_le_div_iff_of_pos_right hpi]; norm_num

/-- **`‖Λ_{a,b}(1)‖ ≤ 6.7/π`, even `a`, odd `b`.** -/
theorem norm_gaussLambda_le_B {a b : ℝ} (ha : a = 0 ∨ a = 1 / 2) (hb : b = 1 / 4 ∨ b = 3 / 4) :
    ‖gaussLambda (a : UnitAddCircle) (b : UnitAddCircle) 1‖ ≤ 6.7 / π := by
  have hpi := Real.pi_pos
  have hpi' := pi_gt'
  have hneg := neg_eq_of_even ha
  have h1 : ‖∫ x in Ioi (1 : ℝ), gaussTheta (a : UnitAddCircle) (b : UnitAddCircle) x‖ ≤
      (0.37 * 1.11) / (π / 16) := by
    refine norm_integral_Ioi_one_le (by positivity) fun x hx => ?_
    rw [gaussTheta, oddKernel_eq_zero_of_neg hneg, ofReal_zero, zero_mul, zero_add,
      norm_mul, Complex.norm_I, one_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have e1 := abs_oddKernel_le hb hx.le
    have e2 := abs_evenKernel_le ha hx.le
    have e0 : 0 ≤ Real.exp (-(π / 16) * (x - 1)) := (Real.exp_pos _).le
    calc |evenKernel (a : UnitAddCircle) x| * |oddKernel (b : UnitAddCircle) x|
        ≤ 1.11 * (0.37 * Real.exp (-(π / 16) * (x - 1))) :=
          mul_le_mul e2 e1 (abs_nonneg _) (by norm_num)
      _ = 0.37 * 1.11 * Real.exp (-(π / 16) * (x - 1)) := by ring
  have h2 : ‖∫ x in Ioi (1 : ℝ), gaussThetaDual (a : UnitAddCircle) (b : UnitAddCircle) x‖ ≤
      (0.112 * 1.11) / π := by
    refine norm_integral_Ioi_one_le hpi fun x hx => ?_
    rw [gaussThetaDual, sinKernel_eq_zero_of_neg hneg, ofReal_zero, zero_mul, zero_add,
      norm_mul, Complex.norm_I, one_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have e1 := abs_sinKernel_le b hx.le
    have e2 := abs_cosKernel_le a hx.le
    have e0 : 0 ≤ Real.exp (-π * (x - 1)) := (Real.exp_pos _).le
    calc |cosKernel (a : UnitAddCircle) x| * |sinKernel (b : UnitAddCircle) x|
        ≤ 1.11 * (0.112 * Real.exp (-π * (x - 1))) :=
          mul_le_mul e2 e1 (abs_nonneg _) (by norm_num)
      _ = 0.112 * 1.11 * Real.exp (-π * (x - 1)) := by ring
  rw [gaussLambda_one_eq]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 0.37 * 1.11 / (π / 16) + 0.112 * 1.11 / π := add_le_add h1 h2
    _ = (0.37 * 1.11 * 16 + 0.112 * 1.11) / π := by field_simp
    _ ≤ 6.7 / π := by rw [div_le_div_iff_of_pos_right hpi]; norm_num

/-! ## §7. `‖L(C₁, 1)‖ ≤ 3.35` and `∫₁^∞ dx/√(x³−x) ≥ 2` -/

theorem unitG_eq_zero_of_parity : ∀ i k : Fin 4, (i.val + k.val) % 2 = 0 →
    unitG (((i : ℤ) : ZMod 4), ((k : ℤ) : ZMod 4)) = 0 := by decide

theorem norm_unitOf_le (t : ZMod 4 × ZMod 4) : ‖unitOf t‖ ≤ 1 := by
  unfold unitOf; split_ifs <;> simp

theorem norm_gaussLambda_le_of_parity (i k : Fin 4) (h : (i.val + k.val) % 2 = 1) :
    ‖gaussLambda (((i : ℝ) / 4 : ℝ) : UnitAddCircle) (((k : ℝ) / 4 : ℝ) : UnitAddCircle) 1‖ ≤
      6.7 / π := by
  rcases i with ⟨i, hi⟩
  rcases k with ⟨k, hk⟩
  simp only at h
  interval_cases i <;> interval_cases k <;> simp only [Nat.reduceAdd, Nat.reduceMod] at h <;>
    first
    | omega
    | (refine norm_gaussLambda_le_A ?_ ?_ <;> norm_num <;> done)
    | (refine norm_gaussLambda_le_B ?_ ?_ <;> norm_num)

/-- The weight of class `j` in the bound. -/
def wv (j : Fin 4 × Fin 4) : ℝ := if (j.1.val + j.2.val) % 2 = 1 then 6.7 / 16 else 0

theorem term_le (j : Fin 4 × Fin 4) :
    ‖cU (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4)) * (1 / 4) *
      ((π : ℂ) * gaussLambda (((j.1 : ℝ) / 4 : ℝ) : UnitAddCircle)
        (((j.2 : ℝ) / 4 : ℝ) : UnitAddCircle) 1)‖ ≤ wv j := by
  have hpi := Real.pi_pos
  by_cases h : (j.1.val + j.2.val) % 2 = 1
  · rw [wv, if_pos h]
    have hΛ := norm_gaussLambda_le_of_parity j.1 j.2 h
    have hc : ‖cU (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4))‖ ≤ 1 / 4 := by
      have := norm_unitOf_le (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4))
      rw [cU, norm_mul, show ‖(1 / 4 : ℂ)‖ = 1 / 4 by norm_num]
      linarith
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
    calc ‖cU (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4))‖ * ‖(1 / 4 : ℂ)‖ *
          (π * ‖gaussLambda (((j.1 : ℝ) / 4 : ℝ) : UnitAddCircle)
            (((j.2 : ℝ) / 4 : ℝ) : UnitAddCircle) 1‖)
        ≤ (1 / 4) * (1 / 4) * (π * (6.7 / π)) := by
          have : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
          rw [this]
          gcongr
      _ = 6.7 / 16 := by field_simp; norm_num
  · rw [wv, if_neg h]
    have hz : unitOf (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4)) = 0 := by
      rw [unitOf_eq_unitG, unitG_eq_zero_of_parity j.1 j.2 (by omega)]; simp
    rw [cU, hz]; simp

theorem sum_wv : ∑ j : Fin 4 × Fin 4, wv j = 3.35 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_four, wv, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num

/-- **`‖L(C₁, 1)‖ ≤ 3.35`** (true value `0.6555…`). -/
theorem norm_lValOne_one_le : ‖ZInQ.Contrib.TYZDecomp.lValOne 1‖ ≤ 3.35 := by
  rw [lValOne_one_eq, ← sum_wv]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => term_le j)

/-- **`∫₁^∞ dx/√(x³ − x) ≥ 2`** (comparison with `∫₁^∞ x^{−3/2} dx = 2`). -/
theorem omegaInt_ge_two : 2 ≤ ZInQ.Contrib.TYZDecomp.omegaInt := by
  have h2 : ∫ x in Ioi (1 : ℝ), x ^ (-(3 / 2 : ℝ)) = 2 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]; norm_num
  rw [← h2, ZInQ.Contrib.TYZDecomp.omegaInt]
  refine setIntegral_mono_on (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one)
    ZInQ.Contrib.TYZDecomp.omegaInt_integrable measurableSet_Ioi fun x (hx : 1 < x) => ?_
  have hx0 : 0 < x := by linarith
  have hpos : 0 < x ^ 3 - x := by
    have := mul_pos (mul_pos hx0 (by linarith : (0:ℝ) < x - 1)) (by linarith : (0:ℝ) < x + 1)
    nlinarith
  have hs : Real.sqrt (x ^ 3) = x ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  rw [Real.rpow_neg hx0.le, ← hs, ← one_div]
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos) (Real.sqrt_le_sqrt (by linarith))


/-! ## §9. `TYZLemma29Mod2` depends only on the parity of `𝓛` -/

open ZInQ.Contrib.PSide in
/-- `LemmaTwoEight` reads `ℓ` only modulo 2 on the squarefree classes `1, 3`. -/
theorem lemmaTwoEight_congr {ℓ ℓ' : ℕ → ℤ}
    (h : ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℤ) : ZMod 2) = ℓ' m)
    (hℓ : LemmaTwoEight ℓ) : LemmaTwoEight ℓ' := by
  constructor
  · intro m hsq hm1 hm
    rw [← hℓ.1 m hsq hm1 hm]
    push_cast
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdm, -⟩, hd8, -⟩ := hd
    have hq8 : m / d % 8 = 1 := by rw [div_mod8_of hdm hm hd8 (Or.inl rfl)]
    rw [h d (hsq.squarefree_of_dvd hdm) (Or.inl hd8),
      h (m / d) (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdm)) (Or.inl hq8)]
  · intro m hsq hm
    rw [← hℓ.2 m hsq hm]
    push_cast
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdm, -⟩, hd8⟩ := hd
    have hq8 : m / d % 8 = 3 := by rw [div_mod8_of hdm hm hd8 (Or.inl rfl)]
    rw [h d (hsq.squarefree_of_dvd hdm) (Or.inl hd8),
      h (m / d) (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdm)) (Or.inr hq8)]

theorem parity_eq_of_sq {a b : ℤ} (h : (a : ℂ) ^ 2 = (b : ℂ) ^ 2) : ((a : ℤ) : ZMod 2) = b := by
  have h' : a ^ 2 = b ^ 2 := by exact_mod_cast h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h' with h1 | h1
  · rw [h1]
  · rw [h1, Int.cast_neg, ZMod.neg_eq_self_mod_two]

/-- **The leaf `TYZLemma29Mod2` is the congruence for one sign choice**: given integrality, the
universally quantified sign choice `ℓ` is immaterial. -/
theorem lemma29Mod2_iff (h11 : TYZThm11Integral) :
    TYZLemma29Mod2 ↔ LemmaTwoEight (ellOf h11) :=
  ⟨fun h => h _ (ellOf_sq h11), fun h ℓ hℓ => lemmaTwoEight_congr
    (fun m hsq hcl => parity_eq_of_sq ((ellOf_sq h11 m hsq hcl).trans (hℓ m hsq hcl).symm)) h⟩

/-! ## §8. The final results -/

/-- **The bound `LValOneBound` holds**: `‖L(C₁,1)‖ ≤ 3.35 < 4.5 ≤ (9/4)·omegaInt`. -/
theorem lValOneBound : LValOneBound := by
  have h1 := norm_lValOne_one_le
  have h2 := omegaInt_ge_two
  unfold LValOneBound
  linarith

/-- **`TYZLcalOne` from the two other L-leaves.** -/
theorem tyzLcalOne_of_leaves (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) : TYZLcalOne :=
  lcalOne_of_leaves h11 h29 lValOneBound

/-- **The premise from three leaves** (`TYZLcalOne` dropped). -/
theorem tyzThm35ReadingA_of_three_leaves (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hG : TYZGenusPackage) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_leaves h11 (tyzLcalOne_of_leaves h11 h29) h29 hG

/-- **Given `TYZThm11Integral` and `TYZLemma29Mod2`, the genus-point package is the premise.** -/
theorem genusPackage_iff_readingA_of_two (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) :
    TYZGenusPackage ↔ ZInQ.Literature.TYZThm35ReadingA :=
  genusPackage_iff_readingA h11 (tyzLcalOne_of_leaves h11 h29) h29

end ZInQ.Contrib.TYZLcal

#print axioms ZInQ.Contrib.TYZLcal.gCl_three
#print axioms ZInQ.Contrib.TYZLcal.ell_one_odd
#print axioms ZInQ.Contrib.TYZLcal.lcalOne_of_leaves
#print axioms ZInQ.Contrib.TYZLcal.isLContinuation_Fone
#print axioms ZInQ.Contrib.TYZLcal.norm_lValOne_one_le
#print axioms ZInQ.Contrib.TYZLcal.omegaInt_ge_two
#print axioms ZInQ.Contrib.TYZLcal.lValOneBound
#print axioms ZInQ.Contrib.TYZLcal.tyzLcalOne_of_leaves
#print axioms ZInQ.Contrib.TYZLcal.tyzThm35ReadingA_of_three_leaves
#print axioms ZInQ.Contrib.TYZLcal.genusPackage_iff_readingA_of_two
#print axioms ZInQ.Contrib.TYZLcal.lemma29Mod2_iff
