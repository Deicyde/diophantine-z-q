import ZInQKernel.Contrib.CloudB3RC53.Basic

/-!
# Lane RC13 (nonvanishing), part 1: vocabulary

The vocabulary of Proposition `ex:sec7-nonvanishing` (tex lines 1968–2004 of the 11/5
manuscript), Proposition `ex:app-five-prime` (Appendix G, lines 9995–10033) and their use in the
rough companion (lines 2343–2401 and 10035–10150). The `L`-function vocabulary is the shared top
layer's (`ZInQ.Contrib.CloudB3RC53`, file `Basic.lean`): the twist `qtwist E d`, the analytic rank
`AnalyticRank E r` (`ord_{s=1} L(E, s) = r` over Mathlib's `WeierstrassCurve.LSeries`), and the
root number `RootNumber E w` (the sign of the functional equation on the strip `0 < Re s < 2`).
This file adds:

* `qtwist_curve`: the twists of `E_ℓ : y² = x(x - ℓ)(x + 3ℓ)` are again curves of the family,
  `qtwist (curve m) d = curve (d * m)`; `qtwist_qtwist`, `qtwist_Δ`, `qtwist_isElliptic`.
* `GoodAt W p`: the model `W` is `p`-integral with discriminant a `p`-adic unit (so `W` has good
  reduction at `p`, Kodaira type `I₀`). Mathlib has no conductor; "a finite set containing the bad
  primes" is rendered as "a finite set containing every prime at which the model is not good";
  `goodAt_twist`, `goodAt_curve`.
* `SplitsIn D p`: the prime `p` splits in `ℚ(√D)`, i.e. the Kronecker symbol `χ_D(p) = 1`.
* `IsFundamentalDiscriminant D` and `omega n` (`ω(n)`, the form of lane RC0's `omega`).
* `CentralNonzero E := AnalyticRank E 0` (`L(E, 1) ≠ 0`); `rootNumber_eq_one_of_centralNonzero`
  (a nonzero central value forces root number `+1`).
* `SignedUnitFilter`: a finite set `S` of primes, a real sign and a unit squareclass at every
  `p ∈ S` (tex 1974–1975), with its membership predicate (`IsSquareAt`: squareclass equality in
  `ℚ_p`) and its root number `SignedUnitFilter.RootNumber`.

Everything in this file is a definition or a PROVED lemma.
-/

namespace ZInQ.Manuscript.RC.Nonvanishing

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53

/-! ### Quadratic twists (the blueprint's `qtwist`) -/

/-- **Twists of `E_ℓ` are curves of the family**: the twist of `y² = x(x - m)(x + 3m)` by `d` is
`y² = x(x - dm)(x + 3dm)`. PROVED. -/
theorem qtwist_curve (m d : ℚ) : qtwist (curve m) d = curve (d * m) := by
  simp only [qtwist, curve, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  ext <;> simp <;> ring

/-- Twisting twice is twisting by the product. PROVED. -/
theorem qtwist_qtwist (W : WeierstrassCurve ℚ) (u d : ℚ) :
    qtwist (qtwist W u) d = qtwist W (d * u) := by
  simp only [qtwist, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  ext <;> simp <;> ring

/-- The discriminant of the twist: `Δ(W^{(d)}) = d⁶ Δ(W)`. PROVED. -/
theorem qtwist_Δ (W : WeierstrassCurve ℚ) (d : ℚ) : (qtwist W d).Δ = d ^ 6 * W.Δ := by
  simp only [qtwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- A twist of an elliptic curve by a nonzero rational is elliptic. PROVED. -/
theorem qtwist_isElliptic {W : WeierstrassCurve ℚ} (hW : W.IsElliptic) {d : ℚ} (hd : d ≠ 0) :
    (qtwist W d).IsElliptic := by
  refine ⟨?_⟩
  rw [qtwist_Δ, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero 6 hd) (isUnit_iff_ne_zero.mp hW.isUnit)

/-- `E_m` is elliptic for `m ≠ 0`. PROVED. -/
theorem curve_isElliptic' {m : ℚ} (hm : m ≠ 0) : (curve m).IsElliptic := by
  refine ⟨?_⟩
  rw [curve_Δ, isUnit_iff_ne_zero]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 6 hm)

/-! ### Good models -/

/-- **The model `W` is good at `p`**: its five coefficients are `p`-integral (`p` does not divide
their denominators) and its discriminant is a nonzero `p`-adic unit. This implies that `W` has
good reduction at `p` (Kodaira type `I₀`). For a model that is not minimal at `p` it is stronger
than good reduction, so "every prime at which the model is not good lies in `S`" is a stronger
requirement on `S` than "every bad prime lies in `S`". -/
def GoodAt (W : WeierstrassCurve ℚ) (p : ℕ) : Prop :=
  ¬ p ∣ W.a₁.den ∧ ¬ p ∣ W.a₂.den ∧ ¬ p ∣ W.a₃.den ∧ ¬ p ∣ W.a₄.den ∧ ¬ p ∣ W.a₆.den ∧
    W.Δ ≠ 0 ∧ padicValRat p W.Δ = 0

/-- `p`-integrality: `p` does not divide the denominator. -/
def PInt (p : ℕ) (x : ℚ) : Prop := ¬ p ∣ x.den

theorem pInt_add {p : ℕ} (hp : p.Prime) {x y : ℚ} (hx : PInt p x) (hy : PInt p y) :
    PInt p (x + y) := fun h =>
  ((Nat.Prime.dvd_mul hp).mp (h.trans (Rat.add_den_dvd x y))).elim hx hy

theorem pInt_mul {p : ℕ} (hp : p.Prime) {x y : ℚ} (hx : PInt p x) (hy : PInt p y) :
    PInt p (x * y) := fun h =>
  ((Nat.Prime.dvd_mul hp).mp (h.trans (Rat.mul_den_dvd x y))).elim hx hy

theorem pInt_intCast {p : ℕ} (hp : p.Prime) (n : ℤ) : PInt p (n : ℚ) := by
  simp only [PInt, Rat.den_intCast, Nat.dvd_one]; exact hp.ne_one

theorem pInt_neg {p : ℕ} {x : ℚ} (hx : PInt p x) : PInt p (-x) := by
  simpa [PInt, Rat.neg_den] using hx

theorem pInt_sub {p : ℕ} (hp : p.Prime) {x y : ℚ} (hx : PInt p x) (hy : PInt p y) :
    PInt p (x - y) := by
  rw [sub_eq_add_neg]; exact pInt_add hp hx (pInt_neg hy)

theorem pInt_pow {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : PInt p x) (n : ℕ) : PInt p (x ^ n) := by
  induction n with
  | zero => simpa using pInt_intCast hp 1
  | succ n ih => rw [pow_succ]; exact pInt_mul hp ih hx

/-- For odd `p`, dividing by `2` or `4` keeps `p`-integrality. -/
theorem pInt_div_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : ℚ} (hx : PInt p x) (k : ℕ) :
    PInt p (x / 2 ^ k) := by
  have hinv : PInt p ((2 : ℚ) ^ k)⁻¹ := by
    have h1 : ((2 : ℚ) ^ k)⁻¹ = ((2 ^ k : ℕ) : ℚ)⁻¹ := by push_cast; rfl
    rw [h1, PInt, Rat.inv_natCast_den]
    split_ifs with h0
    · simp only [Nat.dvd_one]; exact hp.ne_one
    · intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  rw [div_eq_mul_inv]; exact pInt_mul hp hx hinv

/-- **A twist of a good model by an integer prime to `p` is good at `p`** (`p` odd). PROVED. -/
theorem goodAt_twist {W : WeierstrassCurve ℚ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hW : GoodAt W p) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) : GoodAt (qtwist W d) p := by
  obtain ⟨h1, h2, h3, h4, h6, hΔ, hv⟩ := hW
  have i1 : PInt p W.a₁ := h1
  have i2 : PInt p W.a₂ := h2
  have i3 : PInt p W.a₃ := h3
  have i4 : PInt p W.a₄ := h4
  have i6 : PInt p W.a₆ := h6
  have iD : PInt p (d : ℚ) := pInt_intCast hp d
  have i0 : PInt p (0 : ℚ) := by simpa using pInt_intCast hp 0
  have c2 : PInt p (2 : ℚ) := by simpa using pInt_intCast hp 2
  have c4 : PInt p (4 : ℚ) := by simpa using pInt_intCast hp 4
  have hb₂ : PInt p W.b₂ := by
    simp only [WeierstrassCurve.b₂]
    exact pInt_add hp (pInt_pow hp i1 2) (pInt_mul hp c4 i2)
  have hb₄ : PInt p W.b₄ := by
    simp only [WeierstrassCurve.b₄]
    exact pInt_add hp (pInt_mul hp c2 i4) (pInt_mul hp i1 i3)
  have hb₆ : PInt p W.b₆ := by
    simp only [WeierstrassCurve.b₆]
    exact pInt_add hp (pInt_pow hp i3 2) (pInt_mul hp c4 i6)
  have hd0 : (d : ℚ) ≠ 0 := by
    intro h0; apply hd; rw [Int.cast_eq_zero.mp h0]; exact dvd_zero _
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨i0, ?_, i0, ?_, ?_, ?_, ?_⟩
  · change PInt p ((d : ℚ) * W.b₂ / 4)
    have := pInt_div_two_pow hp hp2 (pInt_mul hp iD hb₂) 2
    rwa [show (2 : ℚ) ^ 2 = 4 by norm_num] at this
  · change PInt p ((d : ℚ) ^ 2 * W.b₄ / 2)
    have := pInt_div_two_pow hp hp2 (pInt_mul hp (pInt_pow hp iD 2) hb₄) 1
    rwa [pow_one] at this
  · change PInt p ((d : ℚ) ^ 3 * W.b₆ / 4)
    have := pInt_div_two_pow hp hp2 (pInt_mul hp (pInt_pow hp iD 3) hb₆) 2
    rwa [show (2 : ℚ) ^ 2 = 4 by norm_num] at this
  · rw [qtwist_Δ]; exact mul_ne_zero (pow_ne_zero 6 hd0) hΔ
  · rw [qtwist_Δ, padicValRat.mul (pow_ne_zero 6 hd0) hΔ, padicValRat.pow, hv,
      padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hd]
    simp

/-- **`E_m` (`m ∈ ℤ`) is good at every prime `p ∤ 6m`.** PROVED. -/
theorem goodAt_curve {m : ℤ} {p : ℕ} (hp : p.Prime) (h : ¬ (p : ℤ) ∣ 6 * m) :
    GoodAt (curve m) p := by
  have i0 : PInt p (0 : ℚ) := by simpa using pInt_intCast hp 0
  have hΔ : (curve (m : ℚ)).Δ = ((2304 * m ^ 6 : ℤ) : ℚ) := by rw [curve_Δ]; push_cast; ring
  have hm : m ≠ 0 := by rintro rfl; exact h (by simp)
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨i0, ?_, i0, ?_, i0, ?_, ?_⟩
  · change PInt p (2 * (m : ℚ))
    have := pInt_intCast hp (2 * m); push_cast at this; exact this
  · change PInt p (-3 * (m : ℚ) ^ 2)
    have := pInt_intCast hp (-3 * m ^ 2); push_cast at this; exact this
  · rw [hΔ]; exact_mod_cast (by positivity : (2304 * m ^ 6 : ℤ) ≠ 0)
  · rw [hΔ, padicValRat.of_int, Nat.cast_eq_zero]
    apply padicValInt.eq_zero_of_not_dvd
    intro hdvd
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpZ.dvd_or_dvd hdvd with h1 | h1
    · -- `p ∣ 2304 = 2⁸ 3²` forces `p ∈ {2, 3}`, hence `p ∣ 6m`
      apply h
      have h2304 : (2304 : ℤ) = 2 ^ 8 * 3 ^ 2 := by norm_num
      rw [h2304] at h1
      rcases hpZ.dvd_or_dvd h1 with h2 | h2
      · have := hpZ.dvd_of_dvd_pow h2
        exact Dvd.dvd.mul_right (this.trans (by norm_num : (2 : ℤ) ∣ 6)) m
      · have := hpZ.dvd_of_dvd_pow h2
        exact Dvd.dvd.mul_right (this.trans (by norm_num : (3 : ℤ) ∣ 6)) m
    · exact h (Dvd.dvd.mul_left (hpZ.dvd_of_dvd_pow h1) 6)

/-! ### Splitting, fundamental discriminants, `ω` and signs -/

/-- **`p` splits in `ℚ(√D)`**, i.e. the Kronecker symbol `χ_D(p) = (D/p)` equals `1`: for odd `p`,
`p ∤ D` and `D` is a square modulo `p`; for `p = 2`, `D ≡ 1 (mod 8)`. For a fundamental
discriminant `D` this is the splitting of `p` in `ℚ(√D)` (Dedekind–Kummer). -/
def SplitsIn (D : ℤ) (p : ℕ) : Prop :=
  (p = 2 → D % 8 = 1) ∧ (p ≠ 2 → ¬ (p : ℤ) ∣ D ∧ IsSquare (D : ZMod p))

/-- **Fundamental discriminant**: `D ≠ 1` and either `D ≡ 1 (mod 4)` squarefree, or `D = 4m`
with `m ≡ 2, 3 (mod 4)` squarefree. -/
def IsFundamentalDiscriminant (D : ℤ) : Prop :=
  D ≠ 1 ∧ ((D % 4 = 1 ∧ Squarefree D) ∨
    ∃ m : ℤ, D = 4 * m ∧ (m % 4 = 2 ∨ m % 4 = 3) ∧ Squarefree m)

/-- `ω(n)`: the number of distinct prime factors of `|n|` (the form of lane RC0's `omega`). -/
def omega (n : ℤ) : ℕ := ArithmeticFunction.cardDistinctFactors n.natAbs

theorem sign_mul_of_pos {u d : ℤ} (hd : 0 < d) : Int.sign (u * d) = Int.sign u := by
  rw [Int.sign_mul, Int.sign_eq_one_of_pos hd, mul_one]

/-- An odd fundamental discriminant is squarefree and `≡ 1 (mod 4)`. PROVED. -/
theorem IsFundamentalDiscriminant.squarefree_of_odd {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hodd : Odd D) : Squarefree D ∧ D % 4 = 1 := by
  rcases hD.2 with ⟨h1, h2⟩ | ⟨m, rfl, -, -⟩
  · exact ⟨h2, h1⟩
  · exact absurd hodd (by rw [Int.not_odd_iff_even]; exact ⟨2 * m, by ring⟩)

theorem SplitsIn.two {D : ℤ} (h : SplitsIn D 2) : D % 8 = 1 := h.1 rfl

theorem SplitsIn.not_dvd {D : ℤ} {p : ℕ} (hp : p.Prime) (h : SplitsIn D p) : ¬ (p : ℤ) ∣ D := by
  by_cases hp2 : p = 2
  · subst hp2
    have h8 := h.two
    intro hd
    obtain ⟨k, hk⟩ := hd
    omega
  · exact (h.2 hp2).1

/-! ### `L`-values and root numbers (the blueprint's `AnalyticRank`, `RootNumber`) -/

/-- **`L(E, 1) ≠ 0`**: `ord_{s=1} L(E, s) = 0` in the blueprint's `AnalyticRank` (the form of the
companion hypothesis `FixedFieldPackage.hk`); equivalently the entire continuation does not vanish
at `s = 1` (`centralNonzero_iff`). -/
abbrev CentralNonzero (E : WeierstrassCurve ℚ) : Prop := AnalyticRank E 0

/-- Analytic rank zero is `L(E, 1) ≠ 0` for the entire continuation. PROVED. -/
theorem centralNonzero_iff (E : WeierstrassCurve ℚ) :
    CentralNonzero E ↔ ∃ F : ℂ → ℂ, IsLContinuation E F ∧ F 1 ≠ 0 := by
  constructor
  · rintro ⟨F, hd, he, h0⟩
    refine ⟨F, ⟨hd, he⟩, ?_⟩
    rw [Nat.cast_zero, analyticOrderAt_eq_zero] at h0
    rcases h0 with h | h
    · exact absurd (hd.analyticAt 1) h
    · exact h
  · rintro ⟨F, ⟨hd, he⟩, h1⟩
    exact ⟨F, hd, he, by rw [Nat.cast_zero, analyticOrderAt_eq_zero]; exact Or.inr h1⟩

/-- Two entire continuations of `L(E, s)` agree (identity theorem). PROVED. -/
theorem isLContinuation_unique {E : WeierstrassCurve ℚ} {F G : ℂ → ℂ}
    (hF : IsLContinuation E F) (hG : IsLContinuation E G) : F = G := by
  have hU : {s : ℂ | 3 / 2 < s.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hev : F =ᶠ[nhds (2 : ℂ)] G :=
    Filter.mem_of_superset hU fun s hs => (hF.2 s hs).trans (hG.2 s hs).symm
  funext z
  have hFa := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF.1
  have hGa := Complex.analyticOnNhd_univ_iff_differentiable.mpr hG.1
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa isPreconnected_univ (Set.mem_univ 2) hev
    (Set.mem_univ z)

theorem completedL_one_ne_zero {N : ℕ} (hN : 0 < N) {F : ℂ → ℂ} (h1 : F 1 ≠ 0) :
    completedL N F 1 ≠ 0 := by
  simp only [completedL, Complex.Gamma_one, mul_one]
  have hN' : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  refine mul_ne_zero (mul_ne_zero ?_ ?_) h1
  · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hN'
  · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hpi

/-- **A nonzero central value forces root number `+1`** (the functional equation at `s = 1`).
PROVED. -/
theorem rootNumber_eq_one_of_centralNonzero {E : WeierstrassCurve ℚ} {w : ℤ}
    (hw : RootNumber E w) (hL : CentralNonzero E) : w = 1 := by
  obtain ⟨N, hN, F, hF, hFE⟩ := hw
  obtain ⟨G, hG, hG1⟩ := (centralNonzero_iff E).mp hL
  have hFG : F = G := isLContinuation_unique hF hG
  subst hFG
  have h1 := hFE 1 (by norm_num) (by norm_num)
  norm_num only at h1
  have hne := completedL_one_ne_zero hN hG1
  have hw1 : (w : ℂ) = 1 := by
    have h2 : ((w : ℂ) - 1) * completedL N F 1 = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hne
  exact_mod_cast hw1

/-- **Root number `-1` forces `L(E, 1) = 0`.** PROVED. -/
theorem not_centralNonzero_of_rootNumber {E : WeierstrassCurve ℚ}
    (hw : RootNumber E (-1)) : ¬ CentralNonzero E := fun hL =>
  absurd (rootNumber_eq_one_of_centralNonzero hw hL) (by decide)

/-! ### Signed unit filters -/

/-- **`x` is a square in `ℚ_p`** (for `p` prime; vacuous otherwise). The primality of `p` is an
explicit argument, so that the `p`-adic field is built from it. -/
def IsSquareAt (p : ℕ) (x : ℚ) : Prop := ∀ _ : Fact p.Prime, IsSquare (x : ℚ_[p])

/-- **A signed unit filter** (tex 1974–1975): a finite set `S` of primes, a real sign, and for every
`p ∈ S` a unit squareclass at `p`, represented by an integer `cls p` prime to `p`. -/
structure SignedUnitFilter where
  /-- The finite set of primes where unit squareclasses are prescribed. -/
  S : Finset ℕ
  prime_of_mem : ∀ p ∈ S, p.Prime
  /-- The prescribed real sign. -/
  sign : ℤˣ
  /-- A representative of the prescribed unit squareclass at `p ∈ S`. -/
  cls : ℕ → ℤ
  cls_unit : ∀ p ∈ S, ¬ (p : ℤ) ∣ cls p

namespace SignedUnitFilter

/-- **A parameter `u` lies in the filter**: `u ≠ 0` has the prescribed sign, is a `p`-adic unit at
every `p ∈ S`, and lies in the prescribed squareclass of `ℚ_p` there. -/
def Mem (Φ : SignedUnitFilter) (u : ℤ) : Prop :=
  u ≠ 0 ∧ Int.sign u = (Φ.sign : ℤ) ∧ ∀ p ∈ Φ.S, ¬ (p : ℤ) ∣ u ∧ IsSquareAt p ((u : ℚ) / Φ.cls p)

/-- **The filter has root number `w` for `A`**: every squarefree parameter `u` in the filter twists
`A` to a curve of root number `w` (the blueprint's `RootNumber`). The root-number check of tex 1994–2001 shows that this holds as
soon as it holds for one squarefree parameter in the filter (`rootNumber_of_mem`, part 4). -/
def RootNumber (Φ : SignedUnitFilter) (A : WeierstrassCurve ℚ) (w : ℤ) : Prop :=
  ∀ u : ℤ, Φ.Mem u → Squarefree u → ZInQ.Contrib.CloudB3RC53.RootNumber (qtwist A u) w

end SignedUnitFilter

end ZInQ.Manuscript.RC.Nonvanishing
