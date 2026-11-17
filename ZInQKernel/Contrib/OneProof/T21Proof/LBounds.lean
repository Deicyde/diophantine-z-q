import ZInQKernel.Contrib.OneProof.T21Proof.LValues

/-!
# t21-proof: rigorous bounds on `L(C_1, 1)` and `L(C_3, 1)`

Task t21-proof. For a coefficient table `c_j = (cr_j + ci_j i)/4` on `(ℤ/M)²`,
`L = Σ_j c_j (π/M) Λ_{j/M}(1)` is within `(15.2 e^{−π} + 0.2487)/(4M) · Σ_j (|cr_j| + |ci_j|)` of the
main sum `S = Σ_j c_j (π/M) mainL(j/M)` (`LKernel.lean`), and `Re S`, `Im S` are finite sums
`Σ q E^N` (`E = e^{−π/M²}`, `q ∈ ℚ`) bounded by rational certificates checked by `decide +kernel`
from `l ≤ E ≤ u`.
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

/-! ## Rational enclosures of `q E^N` -/

/-- A rational lower bound of `q E^N` from `l ≤ E ≤ u`. -/
def loQ (q : ℚ) (N : ℕ) (l u : ℚ) : ℚ := if 0 ≤ q then q * l ^ N else q * u ^ N

/-- A rational upper bound of `q E^N` from `l ≤ E ≤ u`. -/
def hiQ (q : ℚ) (N : ℕ) (l u : ℚ) : ℚ := if 0 ≤ q then q * u ^ N else q * l ^ N

theorem loQ_le {q : ℚ} {N : ℕ} {l u : ℚ} {E : ℝ} (hl0 : 0 ≤ l) (hl : (l : ℝ) ≤ E)
    (hu : E ≤ u) : ((loQ q N l u : ℚ) : ℝ) ≤ (q : ℝ) * E ^ N := by
  have hl0' : (0 : ℝ) ≤ l := by exact_mod_cast hl0
  unfold loQ
  split_ifs with hq
  · push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0' hl N) (by exact_mod_cast hq)
  · push_cast
    exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ (hl0'.trans hl) hu N)
      (by exact_mod_cast (not_le.mp hq).le)

theorem le_hiQ {q : ℚ} {N : ℕ} {l u : ℚ} {E : ℝ} (hl0 : 0 ≤ l) (hl : (l : ℝ) ≤ E)
    (hu : E ≤ u) : (q : ℝ) * E ^ N ≤ ((hiQ q N l u : ℚ) : ℝ) := by
  have hl0' : (0 : ℝ) ≤ l := by exact_mod_cast hl0
  unfold hiQ
  split_ifs with hq
  · push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hl0'.trans hl) hu N) (by exact_mod_cast hq)
  · push_cast
    exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hl0' hl N)
      (by exact_mod_cast (not_le.mp hq).le)

/-! ## The imaginary part of a lattice term -/

/-- The rational coefficient `(c_i α₁ + c_r α₂)/(4N)` of `E^N` in the imaginary part. -/
def qIm (cr ci α1 α2 : ℤ) : ℚ :=
  if α1 ^ 2 + α2 ^ 2 = 0 then 0 else ((ci * α1 + cr * α2 : ℤ) : ℚ) / (4 * ((α1 ^ 2 + α2 ^ 2 : ℤ) : ℚ))

theorem im_term (M : ℕ) (hM : 0 < M) (cr ci α1 α2 : ℤ) :
    ((((cr : ℂ) + (ci : ℂ) * I) / 4) * (1 / (M : ℂ)) *
      ((π : ℂ) * tmL ((α1 : ℝ) / M) ((α2 : ℝ) / M))).im =
      (qIm cr ci α1 α2 : ℝ) * Real.exp (-π / (M : ℝ) ^ 2) ^ nQ α1 α2 := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hpi := Real.pi_pos
  unfold qIm nQ tmL
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

theorem re_term' (M : ℕ) (hM : 0 < M) (cr ci α1 α2 : ℤ) (u v : ℝ) (hu : u = (α1 : ℝ) / M)
    (hv : v = (α2 : ℝ) / M) :
    ((((cr : ℂ) + (ci : ℂ) * I) / 4) * (1 / (M : ℂ)) * ((π : ℂ) * tmL u v)).re =
      (qQ cr ci α1 α2 : ℝ) * Real.exp (-π / (M : ℝ) ^ 2) ^ nQ α1 α2 := by
  subst hu hv; exact re_term M hM cr ci α1 α2

theorem im_term' (M : ℕ) (hM : 0 < M) (cr ci α1 α2 : ℤ) (u v : ℝ) (hu : u = (α1 : ℝ) / M)
    (hv : v = (α2 : ℝ) / M) :
    ((((cr : ℂ) + (ci : ℂ) * I) / 4) * (1 / (M : ℂ)) * ((π : ℂ) * tmL u v)).im =
      (qIm cr ci α1 α2 : ℝ) * Real.exp (-π / (M : ℝ) ^ 2) ^ nQ α1 α2 := by
  subst hu hv; exact im_term M hM cr ci α1 α2

/-! ## One class -/

/-- The coefficient `(cr + ci i)/4`. -/
def cC (cr ci : ℤ) : ℂ := ((cr : ℂ) + (ci : ℂ) * I) / 4

/-- The real part of the main term of the class `(j₁, j₂)`: four powers of `E`. -/
def reCl (M : ℕ) (cr ci : ℤ) (j1 j2 : ℕ) (E : ℝ) : ℝ :=
  (qQ cr ci j1 j2 : ℝ) * E ^ nQ j1 j2 + (qQ cr ci j1 (j2 - M) : ℝ) * E ^ nQ j1 (j2 - M) +
    (qQ cr ci (j1 - M) j2 : ℝ) * E ^ nQ (j1 - M) j2 +
    (qQ cr ci (j1 - M) (j2 - M) : ℝ) * E ^ nQ (j1 - M) (j2 - M)

/-- The imaginary part of the main term of the class `(j₁, j₂)`. -/
def imCl (M : ℕ) (cr ci : ℤ) (j1 j2 : ℕ) (E : ℝ) : ℝ :=
  (qIm cr ci j1 j2 : ℝ) * E ^ nQ j1 j2 + (qIm cr ci j1 (j2 - M) : ℝ) * E ^ nQ j1 (j2 - M) +
    (qIm cr ci (j1 - M) j2 : ℝ) * E ^ nQ (j1 - M) j2 +
    (qIm cr ci (j1 - M) (j2 - M) : ℝ) * E ^ nQ (j1 - M) (j2 - M)

theorem cast_sub_div (M j : ℕ) (hM : 0 < M) :
    (j : ℝ) / M - 1 = ((((j : ℤ) - (M : ℤ) : ℤ)) : ℝ) / M := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast; field_simp

theorem re_class (M : ℕ) (hM : 0 < M) (cr ci : ℤ) (j1 j2 : ℕ) :
    (cC cr ci * (1 / (M : ℂ)) * ((π : ℂ) * mainL ((j1 : ℝ) / M) ((j2 : ℝ) / M))).re =
      reCl M cr ci j1 j2 (Real.exp (-π / (M : ℝ) ^ 2)) := by
  unfold mainL cC reCl
  simp only [mul_add, Complex.add_re]
  rw [re_term' M hM cr ci j1 j2 _ _ (by push_cast; rfl) (by push_cast; rfl),
    re_term' M hM cr ci j1 ((j2 : ℤ) - M) _ _ (by push_cast; rfl) (cast_sub_div M j2 hM),
    re_term' M hM cr ci ((j1 : ℤ) - M) j2 _ _ (cast_sub_div M j1 hM) (by push_cast; rfl),
    re_term' M hM cr ci ((j1 : ℤ) - M) ((j2 : ℤ) - M) _ _ (cast_sub_div M j1 hM)
      (cast_sub_div M j2 hM)]

theorem im_class (M : ℕ) (hM : 0 < M) (cr ci : ℤ) (j1 j2 : ℕ) :
    (cC cr ci * (1 / (M : ℂ)) * ((π : ℂ) * mainL ((j1 : ℝ) / M) ((j2 : ℝ) / M))).im =
      imCl M cr ci j1 j2 (Real.exp (-π / (M : ℝ) ^ 2)) := by
  unfold mainL cC imCl
  simp only [mul_add, Complex.add_im]
  rw [im_term' M hM cr ci j1 j2 _ _ (by push_cast; rfl) (by push_cast; rfl),
    im_term' M hM cr ci j1 ((j2 : ℤ) - M) _ _ (by push_cast; rfl) (cast_sub_div M j2 hM),
    im_term' M hM cr ci ((j1 : ℤ) - M) j2 _ _ (cast_sub_div M j1 hM) (by push_cast; rfl),
    im_term' M hM cr ci ((j1 : ℤ) - M) ((j2 : ℤ) - M) _ _ (cast_sub_div M j1 hM)
      (cast_sub_div M j2 hM)]

/-- Rational lower bound of `reCl`. -/
def reClLo (M : ℕ) (cr ci : ℤ) (j1 j2 : ℕ) (l u : ℚ) : ℚ :=
  loQ (qQ cr ci j1 j2) (nQ j1 j2) l u + loQ (qQ cr ci j1 (j2 - M)) (nQ j1 (j2 - M)) l u +
    loQ (qQ cr ci (j1 - M) j2) (nQ (j1 - M) j2) l u +
    loQ (qQ cr ci (j1 - M) (j2 - M)) (nQ (j1 - M) (j2 - M)) l u

/-- Rational upper bound of `reCl`. -/
def reClHi (M : ℕ) (cr ci : ℤ) (j1 j2 : ℕ) (l u : ℚ) : ℚ :=
  hiQ (qQ cr ci j1 j2) (nQ j1 j2) l u + hiQ (qQ cr ci j1 (j2 - M)) (nQ j1 (j2 - M)) l u +
    hiQ (qQ cr ci (j1 - M) j2) (nQ (j1 - M) j2) l u +
    hiQ (qQ cr ci (j1 - M) (j2 - M)) (nQ (j1 - M) (j2 - M)) l u

/-- Rational lower bound of `imCl`. -/
def imClLo (M : ℕ) (cr ci : ℤ) (j1 j2 : ℕ) (l u : ℚ) : ℚ :=
  loQ (qIm cr ci j1 j2) (nQ j1 j2) l u + loQ (qIm cr ci j1 (j2 - M)) (nQ j1 (j2 - M)) l u +
    loQ (qIm cr ci (j1 - M) j2) (nQ (j1 - M) j2) l u +
    loQ (qIm cr ci (j1 - M) (j2 - M)) (nQ (j1 - M) (j2 - M)) l u

/-- Rational upper bound of `imCl`. -/
def imClHi (M : ℕ) (cr ci : ℤ) (j1 j2 : ℕ) (l u : ℚ) : ℚ :=
  hiQ (qIm cr ci j1 j2) (nQ j1 j2) l u + hiQ (qIm cr ci j1 (j2 - M)) (nQ j1 (j2 - M)) l u +
    hiQ (qIm cr ci (j1 - M) j2) (nQ (j1 - M) j2) l u +
    hiQ (qIm cr ci (j1 - M) (j2 - M)) (nQ (j1 - M) (j2 - M)) l u

section bounds
variable {M : ℕ} {cr ci : ℤ} {j1 j2 : ℕ} {l u : ℚ} {E : ℝ}

theorem reClLo_le (hl0 : 0 ≤ l) (hl : (l : ℝ) ≤ E) (hu : E ≤ u) :
    ((reClLo M cr ci j1 j2 l u : ℚ) : ℝ) ≤ reCl M cr ci j1 j2 E := by
  unfold reClLo reCl; push_cast
  gcongr <;> exact loQ_le hl0 hl hu

theorem le_reClHi (hl0 : 0 ≤ l) (hl : (l : ℝ) ≤ E) (hu : E ≤ u) :
    reCl M cr ci j1 j2 E ≤ ((reClHi M cr ci j1 j2 l u : ℚ) : ℝ) := by
  unfold reClHi reCl; push_cast
  gcongr <;> exact le_hiQ hl0 hl hu

theorem imClLo_le (hl0 : 0 ≤ l) (hl : (l : ℝ) ≤ E) (hu : E ≤ u) :
    ((imClLo M cr ci j1 j2 l u : ℚ) : ℝ) ≤ imCl M cr ci j1 j2 E := by
  unfold imClLo imCl; push_cast
  gcongr <;> exact loQ_le hl0 hl hu

theorem le_imClHi (hl0 : 0 ≤ l) (hl : (l : ℝ) ≤ E) (hu : E ≤ u) :
    imCl M cr ci j1 j2 E ≤ ((imClHi M cr ci j1 j2 l u : ℚ) : ℝ) := by
  unfold imClHi imCl; push_cast
  gcongr <;> exact le_hiQ hl0 hl hu

end bounds

/-! ## The whole sum -/

/-- `Σ_j c_j (π/M) Λ_{j/M}(1)`. -/
def Lsum (M : ℕ) (cr ci : ℕ → ℕ → ℤ) : ℂ :=
  ∑ j : Fin M × Fin M, cC (cr j.1 j.2) (ci j.1 j.2) * (1 / (M : ℂ)) *
    ((π : ℂ) * gaussLambda (((j.1 : ℝ) / M : ℝ) : UnitAddCircle) (((j.2 : ℝ) / M : ℝ) : UnitAddCircle) 1)

/-- The main sum `Σ_j c_j (π/M) mainL(j/M)`. -/
def Ssum (M : ℕ) (cr ci : ℕ → ℕ → ℤ) : ℂ :=
  ∑ j : Fin M × Fin M, cC (cr j.1 j.2) (ci j.1 j.2) * (1 / (M : ℂ)) *
    ((π : ℂ) * mainL ((j.1 : ℝ) / M) ((j.2 : ℝ) / M))

theorem norm_cC_le (a b : ℤ) : ‖cC a b‖ ≤ ((|a| + |b| : ℤ) : ℝ) / 4 := by
  unfold cC
  rw [norm_div, show ‖(4 : ℂ)‖ = 4 by norm_num]
  gcongr
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast, Complex.norm_intCast]
  push_cast; rfl

theorem norm_Lsum_sub_Ssum_le (M : ℕ) (hM : 0 < M) (cr ci : ℕ → ℕ → ℤ) :
    ‖Lsum M cr ci - Ssum M cr ci‖ ≤ (15.2 * Real.exp (-π) + 0.2487) / (4 * M) *
      ∑ j : Fin M × Fin M, ((|cr j.1 j.2| + |ci j.1 j.2| : ℤ) : ℝ) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hpi := Real.pi_pos
  unfold Lsum Ssum
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  set a : ℝ := (j.1 : ℝ) / M
  set b : ℝ := (j.2 : ℝ) / M
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have ha1 : a < 1 := by
    rw [div_lt_one hMR]; exact_mod_cast j.1.2
  have hb1 : b < 1 := by
    rw [div_lt_one hMR]; exact_mod_cast j.2.2
  have hΛ := norm_gaussLambda_sub_mainL_le ha0 ha1 hb0 hb1
  have hc := norm_cC_le (cr j.1 j.2) (ci j.1 j.2)
  have e : cC (cr j.1 j.2) (ci j.1 j.2) * (1 / (M : ℂ)) *
        ((π : ℂ) * gaussLambda (a : UnitAddCircle) (b : UnitAddCircle) 1) -
      cC (cr j.1 j.2) (ci j.1 j.2) * (1 / (M : ℂ)) * ((π : ℂ) * mainL a b) =
      cC (cr j.1 j.2) (ci j.1 j.2) * ((1 / (M : ℝ) * π : ℝ) : ℂ) *
        (gaussLambda (a : UnitAddCircle) (b : UnitAddCircle) 1 - mainL a b) := by
    push_cast; ring
  rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  set W : ℝ := ((|cr j.1 j.2| + |ci j.1 j.2| : ℤ) : ℝ)
  have hW : 0 ≤ W := by positivity
  set K : ℝ := 15.2 * Real.exp (-π) + 0.2487
  calc ‖cC (cr j.1 j.2) (ci j.1 j.2)‖ * (1 / (M : ℝ) * π) *
        ‖gaussLambda (a : UnitAddCircle) (b : UnitAddCircle) 1 - mainL a b‖
      ≤ (W / 4) * (1 / (M : ℝ) * π) * (K / π) := by gcongr
    _ = K / (4 * M) * W := by field_simp

/-- The real part of the main sum as a double sum over `range M`. -/
theorem re_Ssum (M : ℕ) (hM : 0 < M) (cr ci : ℕ → ℕ → ℤ) :
    (Ssum M cr ci).re = ∑ j1 ∈ Finset.range M, ∑ j2 ∈ Finset.range M,
      reCl M (cr j1 j2) (ci j1 j2) j1 j2 (Real.exp (-π / (M : ℝ) ^ 2)) := by
  unfold Ssum
  rw [Complex.re_sum, Fintype.sum_prod_type]
  simp only [re_class M hM]
  rw [← Fin.sum_univ_eq_sum_range (fun j1 => ∑ j2 ∈ Finset.range M,
    reCl M (cr j1 j2) (ci j1 j2) j1 j2 (Real.exp (-π / (M : ℝ) ^ 2)))]
  refine Finset.sum_congr rfl fun j1 _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun j2 =>
    reCl M (cr j1 j2) (ci j1 j2) j1 j2 (Real.exp (-π / (M : ℝ) ^ 2))) M

theorem im_Ssum (M : ℕ) (hM : 0 < M) (cr ci : ℕ → ℕ → ℤ) :
    (Ssum M cr ci).im = ∑ j1 ∈ Finset.range M, ∑ j2 ∈ Finset.range M,
      imCl M (cr j1 j2) (ci j1 j2) j1 j2 (Real.exp (-π / (M : ℝ) ^ 2)) := by
  unfold Ssum
  rw [Complex.im_sum, Fintype.sum_prod_type]
  simp only [im_class M hM]
  rw [← Fin.sum_univ_eq_sum_range (fun j1 => ∑ j2 ∈ Finset.range M,
    imCl M (cr j1 j2) (ci j1 j2) j1 j2 (Real.exp (-π / (M : ℝ) ^ 2)))]
  refine Finset.sum_congr rfl fun j1 _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun j2 =>
    imCl M (cr j1 j2) (ci j1 j2) j1 j2 (Real.exp (-π / (M : ℝ) ^ 2))) M

theorem sum_fin_prod {β : Type*} [AddCommMonoid β] (M : ℕ) (f : ℕ → ℕ → β) :
    ∑ j : Fin M × Fin M, f j.1 j.2 = ∑ j1 ∈ Finset.range M, ∑ j2 ∈ Finset.range M, f j1 j2 := by
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range (fun j1 => ∑ j2 ∈ Finset.range M, f j1 j2)]
  exact Finset.sum_congr rfl fun j1 _ => Fin.sum_univ_eq_sum_range (fun j2 => f j1 j2) M

theorem sum_weight (M : ℕ) (cr ci : ℕ → ℕ → ℤ) :
    ∑ j : Fin M × Fin M, ((|cr j.1 j.2| + |ci j.1 j.2| : ℤ) : ℝ) =
      ((∑ j1 ∈ Finset.range M, ∑ j2 ∈ Finset.range M, (|cr j1 j2| + |ci j1 j2|) : ℤ) : ℝ) := by
  have := sum_fin_prod M (fun a b => ((|cr a b| + |ci a b| : ℤ) : ℝ))
  rw [this]; push_cast; rfl

/-- **Generic enclosure.** -/
theorem Lsum_bounds (M : ℕ) (hM : 0 < M) (cr ci : ℕ → ℕ → ℤ) (l u : ℚ) (hl0 : 0 ≤ l)
    (hl : (l : ℝ) ≤ Real.exp (-π / (M : ℝ) ^ 2)) (hu : Real.exp (-π / (M : ℝ) ^ 2) ≤ u)
    (W : ℤ) (hW : ∑ j1 ∈ Finset.range M, ∑ j2 ∈ Finset.range M, (|cr j1 j2| + |ci j1 j2|) = W)
    (rl rh il ih : ℚ)
    (hrl : rl ≤ ∑ j1 ∈ Finset.range M, ∑ j2 ∈ Finset.range M, reClLo M (cr j1 j2) (ci j1 j2) j1 j2 l u)
    (hrh : ∑ j1 ∈ Finset.range M, ∑ j2 ∈ Finset.range M, reClHi M (cr j1 j2) (ci j1 j2) j1 j2 l u ≤ rh)
    (hil : il ≤ ∑ j1 ∈ Finset.range M, ∑ j2 ∈ Finset.range M, imClLo M (cr j1 j2) (ci j1 j2) j1 j2 l u)
    (hih : ∑ j1 ∈ Finset.range M, ∑ j2 ∈ Finset.range M, imClHi M (cr j1 j2) (ci j1 j2) j1 j2 l u ≤ ih) :
    ‖Lsum M cr ci - Ssum M cr ci‖ ≤ (15.2 * Real.exp (-π) + 0.2487) / (4 * M) * W ∧
      (rl : ℝ) ≤ (Ssum M cr ci).re ∧ (Ssum M cr ci).re ≤ rh ∧
      (il : ℝ) ≤ (Ssum M cr ci).im ∧ (Ssum M cr ci).im ≤ ih := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := norm_Lsum_sub_Ssum_le M hM cr ci
    rwa [sum_weight, hW] at this
  · rw [re_Ssum M hM]
    have h := (Rat.cast_le (K := ℝ)).mpr hrl
    push_cast at h
    refine h.trans ?_
    exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => reClLo_le hl0 hl hu
  · rw [re_Ssum M hM]
    have h := (Rat.cast_le (K := ℝ)).mpr hrh
    push_cast at h
    refine le_trans ?_ h
    exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => le_reClHi hl0 hl hu
  · rw [im_Ssum M hM]
    have h := (Rat.cast_le (K := ℝ)).mpr hil
    push_cast at h
    refine h.trans ?_
    exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => imClLo_le hl0 hl hu
  · rw [im_Ssum M hM]
    have h := (Rat.cast_le (K := ℝ)).mpr hih
    push_cast at h
    refine le_trans ?_ h
    exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => le_imClHi hl0 hl hu

end ZInQ.Contrib.T21Proof
