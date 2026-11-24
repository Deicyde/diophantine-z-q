import ZInQKernel.Contrib.PoleRC.DescentM
import ZInQKernel.Model.Descent.Kummer

/-!
# Mordell's theorem for `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)`

Lane R5-mw (fork issue #83). `mordellWeil_curve`: **`E_ℓ(ℚ)` is finitely generated for every
rational `ℓ ≠ 0`.** Consequently the narrowed hypothesis `MordellWeilM` (Mordell's theorem at the
curves `E_ℓ` of Theorem 5.3, the only curves at which `crm_of_restrictedConverse` uses
`MordellWeil`) is a theorem, `mordellWeilM`, and `crm_of_restrictedConverse_M` is the variant of
`crm_of_restrictedConverse` that takes it.

The proof is the textbook one (weak Mordell–Weil by the complete 2-descent, then the descent
theorem with the naive height), on the 2-descent of `E_ℓ` already in `DescentM.lean`:

* `deltaM_eq_one_iff_of_ne_zero`: `ker δ = 2E_ℓ(ℚ)` for every `ℓ ≠ 0`, where
  `δ = deltaM ℓ : P ↦ (x + 3ℓ, x − ℓ)` is the complete 2-descent map (Silverman X.1.4).
  `DescentM.lean` proves this for `ℓ > 0` not a square (`deltaM_eq_one_iff`); the two further
  cases are `x = ℓ` (in the kernel only when `ℓ = m²`, and then `(ℓ, 0) = 2Q` by the halving lemma
  `exists_two_nsmul_eq_M` with square roots `m, 0, 2m`) and `x = 0` (in the kernel only if `3ℓ`
  and `−ℓ` are both squares, impossible for `ℓ ≠ 0`).
* `even_padicValRat_of_sq_eq`, `kum_range_finite`, `range_deltaM_finite`: the image of `δ` is
  finite. With `B = 6 · |num ℓ| · den ℓ`, at a prime `p ∤ B` the pairwise differences `ℓ`, `3ℓ`,
  `4ℓ` of the three factors of `y² = x(x − ℓ)(x + 3ℓ)` are `p`-adic units, so each factor has even
  valuation; each coordinate of `δ(P)` is then the square class of a signed divisor of `B`
  (`sqc_eq_divisor_of_even`, a copy of Route K's former `mwSqc_eq_divisor`) or of `f'(e)` at a
  two-torsion point. This is the inclusion of the image in `K(S, 2) × K(S, 2)`,
  `S = {∞} ∪ {p ∣ B}` (Silverman X.1.4).
* `finiteIndex_two_curve`: `[E_ℓ(ℚ) : 2E_ℓ(ℚ)]` is finite (`E/2E ≅ E/ker δ ≅ δ(E)`).
* `mordellWeil_curve`: Mathlib's descent theorem `AddCommGroup.fg_of_descent'`
  (`GroupTheory/Descent.lean`), with the naive height, the approximate parallelogram law
  `approx_parallelogram_law` and the Northcott property (`NumberTheory/Height/EllipticCurve.lean`).
  These are stated for an arbitrary Weierstrass equation, so `E_ℓ` needs no change of variables;
  the proof is the one of Route K's former `fg_points` for `y² = x³ − d²x`.

Fidelity: the manuscript does not cite Mordell's theorem; it is implicit in
`rank A(ℚ)` (Lemma 5.5, `lem:forward-rank`, `diophantine_zq.tex` lines 1086–1089) and in the
finite Kummer sequence `r + dim Ш[2] = 1` (proof of Lemma 5.4, line 1077), and the application
(lines 1107–1110) uses it only at `E_n` and `E_{nθ}`. Nothing here departs from the manuscript:
the textbook input is proved instead of assumed, at the curves where it is used.
-/

namespace ZInQ.Manuscript.PoleRC

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent ZInQ.RouteK.Rank Height

variable {ℓ : ℚ}

/-! ### `ker δ = 2E_ℓ(ℚ)` for every `ℓ ≠ 0` -/

/-- **`ker δ = 2E_ℓ(ℚ)` for every `ℓ ≠ 0`** (Silverman X.1.4, injectivity of the complete
2-descent map on `E(ℚ)/2E(ℚ)`). Extends `deltaM_eq_one_iff` (`ℓ > 0` not a square). -/
theorem deltaM_eq_one_iff_of_ne_zero (hℓ : ℓ ≠ 0) (P : (curve ℓ).toAffine.Point) :
    deltaM ℓ P = 1 ↔ ∃ Q, 2 • Q = P := by
  constructor
  swap
  · rintro ⟨Q, rfl⟩; exact deltaM_two_nsmul hℓ Q
  intro h1
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, by simp; rfl⟩
  have hf := congrArg Prod.fst h1
  have hs := congrArg Prod.snd h1
  simp only [deltaM, Prod.fst_one, Prod.snd_one, kum_some] at hf hs
  have heq : y ^ 2 = x * (x - ℓ) * (x + 3 * ℓ) := by
    have := (curve_equation_iff x y).mp h.1; rw [this]; ring
  by_cases hx3 : x = -3 * ℓ
  · exfalso
    simp only [hx3, ↓reduceIte, fd] at hf
    rw [show 3 * (-3 * ℓ) ^ 2 + 4 * ℓ * (-3 * ℓ) - 3 * ℓ ^ 2 = 3 * (2 * ℓ) ^ 2 by ring,
      sqc_mul_sq _ (mul_ne_zero two_ne_zero hℓ)] at hf
    exact sqc_ne_one_of_not_isSquare (by norm_num) not_isSquare_three_rat hf
  by_cases hx1 : x = ℓ
  · -- `(ℓ, 0)` lies in the kernel only when `ℓ = m²`; then it is twice a point.
    simp only [hx1, ↓reduceIte, show ℓ ≠ -3 * ℓ from fun h => hℓ (by linarith)] at hf
    rw [show ℓ - -3 * ℓ = ℓ * 2 ^ 2 by ring, sqc_mul_sq _ (by norm_num)] at hf
    obtain ⟨m, hm⟩ := (sqc_eq_one_iff hℓ).mp hf
    exact exists_two_nsmul_eq_M hℓ h (r₁ := m) (r₂ := 0) (r₃ := 2 * m)
      (by rw [hx1, hm]; ring) (by rw [hx1, hm]; ring) (by rw [hx1, hm]; ring)
  simp only [hx3, ↓reduceIte] at hf
  simp only [hx1, ↓reduceIte] at hs
  have hxa : x + 3 * ℓ ≠ 0 := fun h0 => hx3 (by linarith)
  have hxb : x - ℓ ≠ 0 := sub_ne_zero.mpr hx1
  have hf' : sqc (x + 3 * ℓ) = 1 := by rw [show x + 3 * ℓ = x - -3 * ℓ by ring]; exact hf
  obtain ⟨r₃, hr₃⟩ := (sqc_eq_one_iff hxa).mp hf'
  obtain ⟨r₂, hr₂⟩ := (sqc_eq_one_iff hxb).mp hs
  by_cases hx0 : x = 0
  · -- `(0, 0)` would need both `−ℓ` and `3ℓ` to be squares.
    exfalso
    rw [hx0] at hr₂ hr₃
    have h2 : (0 : ℚ) ≤ r₂ * r₂ := mul_self_nonneg _
    have h3 : (0 : ℚ) ≤ r₃ * r₃ := mul_self_nonneg _
    exact hℓ (by linarith)
  have hr0 : r₂ * r₃ ≠ 0 := by
    intro h0
    apply mul_ne_zero hxb hxa
    rw [hr₂, hr₃]; linear_combination (r₂ * r₃) * h0
  exact exists_two_nsmul_eq_M hℓ h (r₁ := y / (r₂ * r₃))
    (by rw [div_pow, eq_div_iff (pow_ne_zero 2 hr0), heq, hr₂, hr₃]; ring)
    (by rw [hr₂]; ring) (by rw [hr₃]; ring)

/-- `ker δ = 2E_ℓ(ℚ)` as an equality of subgroups, for every `ℓ ≠ 0`. -/
theorem deltaHomM_ker_eq_of_ne_zero (hℓ : ℓ ≠ 0) :
    (deltaHomM hℓ).ker = (nsmulAddMonoidHom 2 : (curve ℓ).toAffine.Point →+ _).range := by
  ext P
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  simp only [nsmulAddMonoidHom_apply]
  rw [← deltaM_eq_one_iff_of_ne_zero hℓ P]
  constructor
  · intro h; exact congrArg Additive.toMul h
  · intro h; exact congrArg Additive.ofMul h

/-! ### The image of `δ` is finite -/

/-- **Even valuation away from the bad primes.** If `y² = t (t + d₂)(t + d₃)` with `t ≠ 0` and
`d₂, d₃` units at `p`, then `v_p(t)` is even: if `v_p(t) < 0` the three factors have valuation
`v_p(t)`, if `v_p(t) > 0` the other two are units. -/
theorem even_padicValRat_of_sq_eq {p : ℕ} [Fact p.Prime] {t d₂ d₃ y : ℚ} (ht : t ≠ 0)
    (hd₂ : d₂ ≠ 0) (hd₃ : d₃ ≠ 0) (hv₂ : padicValRat p d₂ = 0) (hv₃ : padicValRat p d₃ = 0)
    (h : y ^ 2 = t * (t + d₂) * (t + d₃)) : Even (padicValRat p t) := by
  have hn : ∀ {d : ℚ}, padicValRat p d = 0 → padicValRat p t ≠ 0 → t + d ≠ 0 := by
    intro d hv ht0 h0
    apply ht0
    rw [show t = -d by linear_combination h0, padicValRat.neg, hv]
  rcases lt_trichotomy (padicValRat p t) 0 with hneg | hzero | hpos
  · have n₂ := hn hv₂ hneg.ne
    have n₃ := hn hv₃ hneg.ne
    have e₂ : padicValRat p (t + d₂) = padicValRat p t :=
      padicValRat.add_eq_of_lt n₂ ht hd₂ (by rw [hv₂]; exact hneg)
    have e₃ : padicValRat p (t + d₃) = padicValRat p t :=
      padicValRat.add_eq_of_lt n₃ ht hd₃ (by rw [hv₃]; exact hneg)
    have hy := congrArg (padicValRat p) h
    rw [padicValRat.pow, padicValRat.mul (mul_ne_zero ht n₂) n₃, padicValRat.mul ht n₂, e₂,
      e₃] at hy
    exact ⟨padicValRat p y - padicValRat p t, by push_cast at hy; omega⟩
  · exact ⟨0, by omega⟩
  · have n₂ := hn hv₂ hpos.ne'
    have n₃ := hn hv₃ hpos.ne'
    have e₂ : padicValRat p (t + d₂) = 0 := by
      rw [add_comm, padicValRat.add_eq_of_lt (by rwa [add_comm]) hd₂ ht (by rw [hv₂]; exact hpos),
        hv₂]
    have e₃ : padicValRat p (t + d₃) = 0 := by
      rw [add_comm, padicValRat.add_eq_of_lt (by rwa [add_comm]) hd₃ ht (by rw [hv₃]; exact hpos),
        hv₃]
    have hy := congrArg (padicValRat p) h
    rw [padicValRat.pow, padicValRat.mul (mul_ne_zero ht n₂) n₃, padicValRat.mul ht n₂, e₂,
      e₃] at hy
    exact ⟨padicValRat p y, by push_cast at hy; omega⟩

/-- A nonzero rational with even valuation at every prime not dividing `B` is a signed divisor
of `B` modulo squares. -/
theorem sqc_eq_divisor_of_even {q : ℚ} (hq : q ≠ 0) {B : ℕ} (hB : B ≠ 0)
    (h : ∀ p : ℕ, p.Prime → ¬p ∣ B → Even (padicValRat p q)) :
    ∃ m : ℤ, m.natAbs ∣ B ∧ sqc q = sqc (m : ℚ) := by
  set N : ℤ := q.num * q.den with hN
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hNq : (N : ℚ) = q * (q.den : ℚ) ^ 2 := by
    rw [hN, Int.cast_mul, ← Rat.mul_den_eq_num]; push_cast; ring
  have hN0 : N ≠ 0 := mul_ne_zero (Rat.num_ne_zero.mpr hq) (by exact_mod_cast q.den_nz)
  obtain ⟨a, s, ha, hs, hsa, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr hN0)
  refine ⟨N.sign * a, ?_, ?_⟩
  · rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hN0, one_mul, Int.natAbs_natCast]
    rw [← Nat.prod_primeFactors_of_squarefree hsq, Nat.prod_primeFactors_dvd_iff hB]
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    refine ⟨hp.1, ?_, hB⟩
    by_contra hpB
    have := Fact.mk hp.1
    obtain ⟨r, hr⟩ := h p hp.1 hpB
    have hvN : padicValRat p (N : ℚ) = padicValRat p q + 2 * padicValRat p (q.den : ℚ) := by
      rw [hNq, padicValRat.mul hq (pow_ne_zero 2 hden), padicValRat.pow]; norm_num
    have hvN' : padicValRat p (N : ℚ) = 2 * padicValNat p s + padicValNat p a := by
      rw [padicValRat.of_int, padicValInt, ← hsa,
        padicValNat.mul (pow_ne_zero 2 hs.ne') ha.ne', padicValNat.pow]
      push_cast; ring
    have h1 := one_le_padicValNat_of_dvd ha.ne' hp.2.1
    have h2 : 2 ≤ padicValNat p a := by
      rw [hvN', hr, padicValRat.of_nat] at hvN
      omega
    have : p * p ∣ a := by
      rw [← pow_two]; exact (pow_dvd_pow p h2).trans pow_padicValNat_dvd
    exact hp.1.one_lt.ne' (Nat.isUnit_iff.mp (hsq p this))
  · rw [← (by rw [hNq, sqc_mul_sq _ hden] : sqc (N : ℚ) = sqc q)]
    conv_lhs => rw [← Int.sign_mul_natAbs N, ← hsa]
    push_cast
    rw [show (N.sign : ℚ) * ((s : ℚ) ^ 2 * a) = N.sign * a * (s : ℚ) ^ 2 by ring,
      sqc_mul_sq _ (by exact_mod_cast hs.ne')]

/-- **The Kummer map of `E_ℓ` at a root `e` has finite image**: its values are the class of
`f'(e)` and the classes of the signed divisors of `B`, provided the other two roots are `e − d₂`
and `e − d₃` with `d₂, d₃` units at every prime not dividing `B`. -/
theorem kum_range_finite {e d₂ d₃ : ℚ} (hd₂ : d₂ ≠ 0) (hd₃ : d₃ ≠ 0)
    (hfac : ∀ x : ℚ, x * (x - ℓ) * (x + 3 * ℓ) = (x - e) * (x - e + d₂) * (x - e + d₃))
    {B : ℕ} (hB : B ≠ 0)
    (hgood : ∀ p : ℕ, p.Prime → ¬ p ∣ B → padicValRat p d₂ = 0 ∧ padicValRat p d₃ = 0) :
    (Set.range (kum ℓ e)).Finite := by
  have hS : ((fun m : ℤ => sqc (m : ℚ)) '' {m : ℤ | m.natAbs ∣ B}).Finite := by
    refine Set.Finite.image _ ((Set.finite_Icc (-(B : ℤ)) B).subset ?_)
    intro m hm
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hB) hm
    simp only [Set.mem_Icc]
    omega
  refine (hS.insert (sqc (fd ℓ e))).subset ?_
  rintro _ ⟨P, rfl⟩
  rcases P with _ | ⟨x, y, h⟩
  · refine Set.mem_insert_of_mem _ ⟨1, by simp, ?_⟩
    show sqc ((1 : ℤ) : ℚ) = 1
    rw [Int.cast_one, sqc_one]
  by_cases hx : x = e
  · rw [kum_some_eq h hx]
    exact Set.mem_insert _ _
  rw [kum_some_of_ne h hx]
  have heq : y ^ 2 = x * (x - ℓ) * (x + 3 * ℓ) := by
    have := (curve_equation_iff x y).mp h.1; rw [this]; ring
  rw [hfac] at heq
  have hxe : x - e ≠ 0 := sub_ne_zero.mpr hx
  obtain ⟨m, hm, hsq⟩ := sqc_eq_divisor_of_even hxe hB fun p hp hpB => by
    have := Fact.mk hp
    obtain ⟨h₂, h₃⟩ := hgood p hp hpB
    exact even_padicValRat_of_sq_eq hxe hd₂ hd₃ h₂ h₃ heq
  exact Set.mem_insert_of_mem _ ⟨m, hm, hsq.symm⟩

private theorem padicValRat_three_four {p : ℕ} [hp : Fact p.Prime] (h6 : ¬ p ∣ 6) :
    padicValRat p (3 : ℚ) = 0 ∧ padicValRat p (4 : ℚ) = 0 := by
  have h2 : ¬ p ∣ 2 := fun h => h6 (h.trans (by norm_num))
  have h3 : ¬ p ∣ 3 := fun h => h6 (h.trans (by norm_num))
  have h4 : ¬ p ∣ 4 := fun h =>
    h2 (hp.out.dvd_of_dvd_pow (n := 2) (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact h))
  constructor
  · rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd h3]
    rfl
  · rw [show (4 : ℚ) = ((4 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd h4]
    rfl

private theorem padicValRat_mul_eq_zero {p : ℕ} [Fact p.Prime] {c q : ℚ} (hc : c ≠ 0) (hq : q ≠ 0)
    (hvc : padicValRat p c = 0) (hvq : padicValRat p q = 0) : padicValRat p (c * q) = 0 := by
  rw [padicValRat.mul hc hq, hvc, hvq, add_zero]

/-- **The image of the complete 2-descent map is finite** (`ℓ ≠ 0`): both coordinates of `δ(P)`
lie in the square classes of the signed divisors of `6 · |num ℓ| · den ℓ` and of `f'(e)`. -/
theorem range_deltaM_finite (hℓ : ℓ ≠ 0) : (Set.range (deltaM ℓ)).Finite := by
  obtain ⟨B, hB, hgood⟩ : ∃ B : ℕ, B ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ B →
      padicValRat p (3 : ℚ) = 0 ∧ padicValRat p (4 : ℚ) = 0 ∧ padicValRat p ℓ = 0 := by
    refine ⟨6 * ℓ.num.natAbs * ℓ.den,
      mul_ne_zero (mul_ne_zero (by norm_num) (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hℓ)))
        ℓ.den_nz, ?_⟩
    intro p hp hpB
    have := Fact.mk hp
    have h6 : ¬ p ∣ 6 := fun h => hpB ((h.mul_right _).mul_right _)
    have hn : ¬ p ∣ ℓ.num.natAbs := fun h => hpB ((h.mul_left 6).mul_right _)
    have hd : ¬ p ∣ ℓ.den := fun h => hpB (h.mul_left _)
    obtain ⟨h3, h4⟩ := padicValRat_three_four h6
    refine ⟨h3, h4, ?_⟩
    rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hn,
      padicValNat.eq_zero_of_not_dvd hd]
    rfl
  have h1 : (Set.range (kum ℓ (-3 * ℓ))).Finite :=
    kum_range_finite (d₂ := -3 * ℓ) (d₃ := -4 * ℓ) (mul_ne_zero (by norm_num) hℓ)
      (mul_ne_zero (by norm_num) hℓ) (fun x => by ring) hB fun p hp hpB => by
        have := Fact.mk hp
        obtain ⟨h3, h4, hv⟩ := hgood p hp hpB
        exact ⟨padicValRat_mul_eq_zero (by norm_num) hℓ (by rw [padicValRat.neg]; exact h3) hv,
          padicValRat_mul_eq_zero (by norm_num) hℓ (by rw [padicValRat.neg]; exact h4) hv⟩
  have h2 : (Set.range (kum ℓ ℓ)).Finite :=
    kum_range_finite (d₂ := ℓ) (d₃ := 4 * ℓ) hℓ (mul_ne_zero (by norm_num) hℓ)
      (fun x => by ring) hB fun p hp hpB => by
        have := Fact.mk hp
        obtain ⟨-, h4, hv⟩ := hgood p hp hpB
        exact ⟨hv, padicValRat_mul_eq_zero (by norm_num) hℓ h4 hv⟩
  refine (h1.prod h2).subset ?_
  rintro _ ⟨P, rfl⟩
  exact ⟨⟨P, rfl⟩, ⟨P, rfl⟩⟩

/-! ### Weak Mordell–Weil and Mordell's theorem for `E_ℓ` -/

/-- **`[E_ℓ(ℚ) : 2E_ℓ(ℚ)]` is finite** for every `ℓ ≠ 0`: the weak Mordell–Weil theorem for `E_ℓ`
and `m = 2` (Silverman, Theorem VIII.1.1, UNVERIFIED numbering), here by the complete 2-descent
(Silverman X.1.4): `E/2E ≅ E/ker δ ≅ δ(E)`, finite by `range_deltaM_finite`. -/
theorem finiteIndex_two_curve (hℓ : ℓ ≠ 0) :
    (nsmulAddMonoidHom 2 : (curve ℓ).toAffine.Point →+ _).range.FiniteIndex := by
  rw [← deltaHomM_ker_eq_of_ne_zero hℓ]
  have hfin : (Set.range (deltaHomM hℓ)).Finite :=
    ((range_deltaM_finite hℓ).image Additive.ofMul).subset (by
      rintro _ ⟨P, rfl⟩
      exact ⟨deltaM ℓ P, ⟨P, rfl⟩, rfl⟩)
  have : Finite (deltaHomM hℓ).range := by
    rw [← AddMonoidHom.coe_range] at hfin
    exact hfin.to_subtype
  infer_instance

/-- **Mordell's theorem for `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)`**: for every rational `ℓ ≠ 0`, the group
`E_ℓ(ℚ)` is finitely generated (Mordell 1922; Silverman, *The Arithmetic of Elliptic Curves*,
Theorem VIII.6.7, UNVERIFIED numbering). Proof: Mathlib's descent theorem
`AddCommGroup.fg_of_descent'` with the naive height, its approximate parallelogram law and the
Northcott property over `ℚ`, and the finite index `finiteIndex_two_curve`. -/
theorem mordellWeil_curve : ∀ ℓ : ℚ, ℓ ≠ 0 → AddGroup.FG (curve ℓ).toAffine.Point := by
  intro ℓ hℓ
  have := curve_isElliptic hℓ
  obtain ⟨C, hC⟩ := approx_parallelogram_law (curve ℓ).toAffine
  exact AddCommGroup.fg_of_descent' (finiteIndex_two_curve hℓ)
    (fun P => by rw [Point.naiveHeight_eq_logHeight]; exact logHeight_nonneg _) hC

/-! ### The narrowed hypothesis and the `CR_M` variant -/

/-- **Mordell's theorem at the curves of Theorem 5.3**: for positive squarefree `ℓ ≡ 11 (mod 12)`,
`E_ℓ(ℚ)` is finitely generated. This is `MordellWeil` restricted to the curves at which
`crm_of_restrictedConverse` uses it (`mordellWeilM_of_mordellWeil`); it is proved
(`mordellWeilM`). -/
def MordellWeilM : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → AddGroup.FG (curve (ℓ : ℚ)).toAffine.Point

/-- The textbook statement `MordellWeil` implies the narrowed one. -/
theorem mordellWeilM_of_mordellWeil (h : MordellWeil) : MordellWeilM :=
  fun ℓ hℓ _ _ => h _ (curve_isElliptic (by exact_mod_cast hℓ.ne'))

/-- **`MordellWeilM` holds** (`mordellWeil_curve`). -/
theorem mordellWeilM : MordellWeilM :=
  fun ℓ hℓ _ _ => mordellWeil_curve ℓ (by exact_mod_cast hℓ.ne')

/-- **`CR_M` from Theorem 5.3, Lemma 5.4 and Lemma 5.5, with Mordell's theorem only at `E_ℓ`.**
The proof of `crm_of_restrictedConverse` (`CRM.lean`, `diophantine_zq.tex` lines 1076–1110), with
`MordellWeilM` in place of `MordellWeil`. -/
theorem crm_of_restrictedConverse_M (SelmerCorankOne : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse SelmerCorankOne) (h54 : Lemma54At SelmerCorankOne)
    (hK : KolyvaginRankOne) (hMW : MordellWeilM) (hD : DescentGlueM) : CRM := by
  intro ℓ hℓ hsf h12 h8 β hβ
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hE := curve_isElliptic hℓ0
  have hP := h54 ℓ hℓ hsf h12 h8
  have hA := hRC ℓ hℓ hsf h12 hP
  have hr := hK _ hE hA
  exact hD ℓ hℓ hsf h12 (hMW ℓ hℓ hsf h12) (exists_not_isOfFinAddOrder_of_rank hr) h8 (β, 1) hβ

/-- **`CR_M` from Theorem 5.3, Lemma 5.4 and Lemma 5.5 alone**: Mordell's theorem at `E_ℓ`
(`mordellWeilM`) and the complete 2-descent (`descentGlueM`) are proved. -/
theorem crm_of_restrictedConverse_proved (SelmerCorankOne : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse SelmerCorankOne) (h54 : Lemma54At SelmerCorankOne)
    (hK : KolyvaginRankOne) : CRM :=
  crm_of_restrictedConverse_M SelmerCorankOne hRC h54 hK mordellWeilM descentGlueM

end ZInQ.Manuscript.PoleRC
