import ZInQKernel.Contrib.OneProof.T21Proof.LKernel

/-!
# t21-proof: `L(C_1, 1)` and `L(C_3, 1)` to within explicit bounds

Task t21-proof. `L(C_d, 1) = Σ_j c_j (π/M) Λ_{j/M}(1)` (`M = 4d`, `c = twChar d`, Hecke's continuation
of `Contrib/HeckeFE`); `Λ_{a,b}(1) = mainL a b + O(1)` (`LKernel.lean`); the main sum is a finite
sum `Σ q_x E^{N_x}`, `E = e^{−π/M²}`, bounded with a kernel-checked rational certificate (`decide`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open Complex Real Set MeasureTheory HurwitzZeta ZInQ.Contrib.HeckeFE ZInQ.Contrib.TYZLcal
open ZInQ.Contrib.HeckeAll

/-! ## The continuation of `L(C_3, s)` -/

theorem isLContinuation_twChar {d : ℕ} (hsq : Squarefree d) [NeZero d] [NeZero (4 * d)] :
    ZInQ.Literature.IsLContinuation (ZInQ.Contrib.TYZDecomp.curveC d) (Fexp (4 * d) (twChar d)) := by
  refine ⟨differentiable_Fexp _ _, fun s hs => ?_⟩
  have hD1 : DeuringCd 1 := deuringCd_of_gaussPointCount (by norm_num) squarefree_one
    ZInQ.Contrib.GaussFE.gaussPointCount
  rw [Fexp_eq_twistedL _ _ hs, ZInQ.Contrib.TYZDecomp.curveC, LSeries_cd_eq' hsq s]
  refine (LSeries_eq_twistedL (4 * d) (twChar d) _ (fun n hn => ?_) hs).symm
  rw [cdCoeff_twist d hn, hD1 n hn, heckeCoeff, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [twChar_intCast hq, jacobiSym.one_right]
  push_cast
  ring

instance : NeZero (4 * 3) := ⟨by norm_num⟩

/-- **`L(C_3, 1)` as a finite combination of the `Λ_{a,b}(1)`.** -/
theorem lValOne_three_eq : ZInQ.Contrib.TYZDecomp.lValOne 3 =
    ∑ j : Fin 12 × Fin 12, twChar 3 (((j.1 : ℤ) : ZMod (4 * 3)), ((j.2 : ℤ) : ZMod (4 * 3))) *
      (1 / 12) * ((π : ℂ) * gaussLambda (((j.1 : ℝ) / 12 : ℝ) : UnitAddCircle)
        (((j.2 : ℝ) / 12 : ℝ) : UnitAddCircle) 1) := by
  rw [ZInQ.Contrib.TYZDecomp.lValOne_eq (isLContinuation_twChar (d := 3) Nat.prime_three.squarefree), Fexp]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [cpow_one, Complex.Gamma_one, inv_one, mul_one]
  push_cast
  norm_num

/-! ## Coefficient tables -/

/-- `Re (4 · unitOf)` on residues mod 4. -/
def uRe (a b : ℕ) : ℤ :=
  if (a % 4, b % 4) = (1, 0) ∨ (a % 4, b % 4) = (3, 2) then 1
  else if (a % 4, b % 4) = (3, 0) ∨ (a % 4, b % 4) = (1, 2) then -1 else 0

/-- `Im (unitOf)` on residues mod 4. -/
def uIm (a b : ℕ) : ℤ :=
  if (a % 4, b % 4) = (0, 3) ∨ (a % 4, b % 4) = (2, 1) then 1
  else if (a % 4, b % 4) = (0, 1) ∨ (a % 4, b % 4) = (2, 3) then -1 else 0

/-- `(3/n)` for odd `n`, by `n mod 12`. -/
def jac12 (n : ℕ) : ℤ :=
  if n % 12 = 1 ∨ n % 12 = 11 then 1 else if n % 12 = 5 ∨ n % 12 = 7 then -1 else 0

theorem unitOf_cast (a b : ℕ) :
    unitOf (((a : ℤ) : ZMod 4), ((b : ℤ) : ZMod 4)) = (uRe a b : ℂ) + (uIm a b : ℂ) * I := by
  have ha : ((a : ℤ) : ZMod 4) = ((a % 4 : ℕ) : ZMod 4) := by
    rw [Int.cast_natCast, ZMod.natCast_mod]
  have hb : ((b : ℤ) : ZMod 4) = ((b % 4 : ℕ) : ZMod 4) := by
    rw [Int.cast_natCast, ZMod.natCast_mod]
  have hu : uRe a b = uRe (a % 4) (b % 4) := by simp [uRe, Nat.mod_mod]
  have hv : uIm a b = uIm (a % 4) (b % 4) := by simp [uIm, Nat.mod_mod]
  rw [ha, hb, hu, hv]
  have h4a : a % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h4b : b % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize a % 4 = r at h4a ⊢
  generalize b % 4 = t at h4b ⊢
  interval_cases r <;> interval_cases t <;> simp (config := {decide := true}) [unitOf, uRe, uIm]

theorem jacobiSym_three_eq {N : ℕ} (hN : Odd N) : jacobiSym 3 N = jac12 N := by
  rw [jacobiSym.mod_right 3 hN]
  have h12 : (4 * (3 : ℤ).natAbs) = 12 := by norm_num
  rw [h12]
  have hlt : N % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hodd : N % 12 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 12)]; exact Nat.odd_iff.mp hN
  have hj : jac12 N = jac12 (N % 12) := by simp [jac12, Nat.mod_mod]
  rw [hj]
  generalize N % 12 = r at hlt hodd ⊢
  interval_cases r <;> simp_all [jac12] <;> norm_num

theorem odd_of_u_ne : ∀ j1 j2 : Fin 12, (uRe j1 j2 ≠ 0 ∨ uIm j1 j2 ≠ 0) →
    ((j1 : ℕ) ^ 2 + (j2 : ℕ) ^ 2) % 2 = 1 := by
  decide

/-- **The coefficients of `L(C_3, s)`**: `twChar 3 j = (cr + ci·i)/4`. -/
theorem twChar_three_eq (j1 j2 : Fin 12) :
    twChar 3 (((j1 : ℕ) : ℤ), ((j2 : ℕ) : ℤ)) =
      (((jac12 ((j1 : ℕ) ^ 2 + (j2 : ℕ) ^ 2) * uRe j1 j2 : ℤ) : ℂ) +
        ((jac12 ((j1 : ℕ) ^ 2 + (j2 : ℕ) ^ 2) * uIm j1 j2 : ℤ) : ℂ) * I) / 4 := by
  have hv1 : (((j1 : ℕ) : ℤ) : ZMod (4 * 3)).val = j1 := by
    rw [Int.cast_natCast, ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by have := j1.2; omega)
  have hv2 : (((j2 : ℕ) : ℤ) : ZMod (4 * 3)).val = j2 := by
    rw [Int.cast_natCast, ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by have := j2.2; omega)
  simp only [twChar, hv1, hv2]
  rw [unitOf_cast]
  by_cases hu : uRe j1 j2 ≠ 0 ∨ uIm j1 j2 ≠ 0
  · have hN := odd_of_u_ne j1 j2 hu
    erw [jacobiSym_three_eq (Nat.odd_iff.mpr hN)]
    push_cast; ring
  · push_neg at hu
    rw [hu.1, hu.2]; push_cast; ring

theorem cU_eq (j1 j2 : Fin 4) :
    cU (((j1 : ℕ) : ℤ), ((j2 : ℕ) : ℤ)) =
      (((uRe j1 j2 : ℤ) : ℂ) + ((uIm j1 j2 : ℤ) : ℂ) * I) / 4 := by
  have e1 : ((((j1 : ℕ) : ℤ) : ZMod 4)) = (((j1 : ℕ) : ℤ) : ZMod 4) := rfl
  simp only [cU]
  rw [unitOf_cast]; ring

/-! ## The real part of the main sum -/

/-- The rational coefficient `q = (c_r α₁ − c_i α₂)/(4N)` of `E^N`, `N = α₁² + α₂²`. -/
def qQ (cr ci α1 α2 : ℤ) : ℚ :=
  if α1 ^ 2 + α2 ^ 2 = 0 then 0 else ((cr * α1 - ci * α2 : ℤ) : ℚ) / (4 * ((α1 ^ 2 + α2 ^ 2 : ℤ) : ℚ))

/-- `N = α₁² + α₂²`. -/
def nQ (α1 α2 : ℤ) : ℕ := (α1 ^ 2 + α2 ^ 2).toNat

theorem re_term (M : ℕ) (hM : 0 < M) (cr ci α1 α2 : ℤ) :
    ((((cr : ℂ) + (ci : ℂ) * I) / 4) * (1 / (M : ℂ)) *
      ((π : ℂ) * tmL ((α1 : ℝ) / M) ((α2 : ℝ) / M))).re =
      (qQ cr ci α1 α2 : ℝ) * Real.exp (-π / (M : ℝ) ^ 2) ^ nQ α1 α2 := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hpi := Real.pi_pos
  unfold qQ nQ tmL
  by_cases hN : α1 ^ 2 + α2 ^ 2 = 0
  · have h1 : α1 = 0 := by nlinarith [sq_nonneg α1, sq_nonneg α2]
    have h2 : α2 = 0 := by nlinarith [sq_nonneg α1, sq_nonneg α2]
    subst h1; subst h2
    simp
  · rw [if_neg hN]
    have hNpos : 0 < α1 ^ 2 + α2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hN)
    have hNR : (0 : ℝ) < (α1 : ℝ) ^ 2 + (α2 : ℝ) ^ 2 := by exact_mod_cast hNpos
    have hnat : ((α1 ^ 2 + α2 ^ 2).toNat : ℝ) = (α1 : ℝ) ^ 2 + (α2 : ℝ) ^ 2 := by
      have : (((α1 ^ 2 + α2 ^ 2).toNat : ℤ) : ℝ) = ((α1 ^ 2 + α2 ^ 2 : ℤ) : ℝ) := by
        rw [Int.toNat_of_nonneg hNpos.le]
      push_cast at this; exact this
    rw [← Real.exp_nat_mul, hnat]
    have hexp : Real.exp (-π * (((α1 : ℝ) / M) ^ 2 + ((α2 : ℝ) / M) ^ 2)) =
        Real.exp (((α1 : ℝ) ^ 2 + (α2 : ℝ) ^ 2) * (-π / (M : ℝ) ^ 2)) := by
      congr 1; field_simp
    rw [hexp]
    set X := Real.exp (((α1 : ℝ) ^ 2 + (α2 : ℝ) ^ 2) * (-π / (M : ℝ) ^ 2))
    have hden : π * (((α1 : ℝ) / M) ^ 2 + ((α2 : ℝ) / M) ^ 2) =
        π * ((α1 : ℝ) ^ 2 + (α2 : ℝ) ^ 2) / (M : ℝ) ^ 2 := by field_simp
    rw [hden]
    simp only [Complex.mul_re, Complex.div_re, Complex.add_re, Complex.add_im, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_im, Complex.one_re, Complex.one_im, Complex.natCast_re,
      Complex.natCast_im, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat,
      Complex.normSq_natCast]
    push_cast
    field_simp
    ring

end ZInQ.Contrib.T21Proof
