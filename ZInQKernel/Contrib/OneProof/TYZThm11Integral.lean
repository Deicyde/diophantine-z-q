import ZInQKernel.Contrib.OneProof.TYZLemma29Mod2

/-!
# `TYZThm11Integral` (TYZ Theorem 1.1, integrality) from Lemma 2.9 and Tunnell's formula

Task h11-reduce; report `docs/research/h11-reduce.md`, log and computations in `scratch/h11-reduce/`.

Tian–Yuan–Zhang (TYZ), *Genus periods, genus points and congruent number problem*, arXiv:1411.4728v1,
Asian J. Math. 21 (2017). Line numbers `Lnnnn` refer to the arXiv source `Period7.tex`; they are quoted from
earlier notes (`docs/research/h29-fix.md`, `h29-ne3.md`, `rv-pn-encoding.md`); the source was not on this host.

The top hypothesis `h11 = ZInQ.Contrib.TYZDecomp.TYZThm11Integral` of `ZInQ.OneProof.frozenTarget`
(`𝓛(m)` is an integer for squarefree `m ≡ 1, 3 (mod 8)`) is proved (`tyzThm11Integral_of_leaves`) from

* `TYZLemma29PrintedNe3R`: TYZ Lemma 2.9 (L1062–1066) as printed, for squarefree `1 < n ≡ 1, 3 (mod 8)`,
  `n ≠ 3`, for every **real** sign choice of `𝓛` (TYZ's `𝓛(n)` is a real number, a square root of
  `L(E_n, 1)/(2^{2k−2−a}Ω_n)`, L338–353). It is the open leaf `TYZLemma29PrintedNe3` with the sign choices
  `ℓ : ℕ → ℝ` instead of `ℓ : ℕ → ℤ`, and implies it (`tyzLemma29PrintedNe3_of_R`). The integer form
  presupposes Theorem 1.1 (without integrality there is no integer sign choice and the leaf is vacuous), so it
  cannot give Theorem 1.1; the real form is the print.
* `TunnellOddL1`: Tunnell's formula, J. B. Tunnell, *A classical Diophantine problem and modular forms of
  weight 3/2*, Invent. Math. 72 (1983), 323–334 (theorem number UNVERIFIED): for odd squarefree `n`,
  `L(C_n, 1) = β (A(n) − 2B(n))² / (16√n)`, `β = ∫₁^∞ dx/√(x³ − x)`, `A(n) = #{2x² + y² + 8z² = n}`,
  `B(n) = #{2x² + y² + 32z² = n}` (triples of integers). Checked numerically on 30 odd squarefree `n ≤ 187`
  of every class mod 8 (`scratch/h11-reduce/tunnell_check.py`, PARI, 38 digits: difference `≤ 2·10⁻¹⁹`).
* `LegendreThreeSquares`, `JonesPallX2Y2Z16`, `TYZTestVectorExists` (already open; they give TYZ's embedding
  `τ` and test vector `f_n`, the objects of Lemma 2.9).

The proof is TYZ's (L1081–1088, as reported in `rv-pn-encoding.md`): induction on the divisors. Lemma 2.9 at
`n` reads `±𝓛(n)𝓛(1) + Σ_{d ≠ 1} ±𝓛(n/d)𝓛(d) = Q(n) ∈ ℤ`, and the other terms are integers by induction.
TYZ's print fails at `n = 3` (Lemma 2.9 is false there, h29-fix) and uses `𝓛(1) = 1` (L1082, asserted); both
values come from Tunnell's formula: `A(1) = B(1) = 2` and `A(3) = B(3) = 4` give `𝓛(1)² = 𝓛(3)² = 1`. The
sign choice used is Tunnell's `ℓ(m) = (A(m) − 2B(m))/2^{k(m)+1}` (`ellR`), real by the formula.

The same leaves also give `h29 = TYZLemma29Mod2` without TYZ Theorem 2.1 at `(3, 1)`
(`tyzLemma29Mod2_of_tunnell`): at `m = 3` the congruence is `𝓛(3)𝓛(1) ≡ g(3) = 1`, and `𝓛(3)𝓛(1) = ±1`.
So `frozenTarget`'s arguments `h11`, `hL29` and `hT21` are replaced by `TYZLemma29PrintedNe3R` and
`TunnellOddL1` (`scratch/h11-reduce/MainEdit.lean`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZDecomp.H11Reduce

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZDecomp.H29Split
  NumberField IsDedekindDomain
open scoped Quaternion

/-! ## §1. The leaves -/

/-- Tunnell's `A(n) = #{(x, y, z) ∈ ℤ³ : 2x² + y² + 8z² = n}`. -/
def tunnellA (n : ℕ) : ℕ :=
  Nat.card {v : ℤ × ℤ × ℤ // 2 * v.1 ^ 2 + v.2.1 ^ 2 + 8 * v.2.2 ^ 2 = (n : ℤ)}

/-- Tunnell's `B(n) = #{(x, y, z) ∈ ℤ³ : 2x² + y² + 32z² = n}`. -/
def tunnellB (n : ℕ) : ℕ :=
  Nat.card {v : ℤ × ℤ × ℤ // 2 * v.1 ^ 2 + v.2.1 ^ 2 + 32 * v.2.2 ^ 2 = (n : ℤ)}

/-- **Tunnell's formula for odd `n`** (J. B. Tunnell, *A classical Diophantine problem and modular forms of
weight 3/2*, Invent. Math. 72 (1983), 323–334; the L-value formula for odd squarefree `n`, theorem number
UNVERIFIED; also in N. Koblitz, *Introduction to elliptic curves and modular forms*, GTM 97, Ch. IV, locator
UNVERIFIED): for odd squarefree `n`,
`L(C_n, 1) = β (A(n) − 2B(n))² / (16√n)`, with `C_n : y² = x³ − n²x`, `β = ∫₁^∞ dx/√(x³ − x)` (`omegaInt`) and
the representation numbers `A(n)`, `B(n)` above. `L(C_n, 1)` is `lValOne n`, the value at `s = 1` of the
continuation of Mathlib's `L(C_n, s)` (it exists, `ZInQ.Contrib.heckeContinuation`, and is unique).

Equivalent forms in the literature: `β (B(n) − A(n)/2)²/(4√n)`, and `β a(n)²/(4√n)` with `a(n)` the `n`-th
coefficient of `η(8z)η(16z)θ(2z)` (`a(n) = B(n) − A(n)/2` for odd `n`). Checked numerically on 30 odd squarefree
`n ≤ 187`, every class mod 8 (`scratch/h11-reduce/tunnell_check.py`, PARI `lfun` at 38 digits; largest
difference `2·10⁻¹⁹`). Only `n = 1` and `n = 3` are used. -/
def TunnellOddL1 : Prop :=
  ∀ n : ℕ, Odd n → Squarefree n →
    lValOne n = (omegaInt : ℂ) * ((tunnellA n : ℂ) - 2 * (tunnellB n : ℂ)) ^ 2 /
      (16 * (Real.sqrt n : ℂ))

/-- `ℓ` is a real sign choice of TYZ's `𝓛` on the squarefree classes `1, 3 (mod 8)`. -/
def IsLcalSignR (ℓ : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m

/-- **TYZ Lemma 2.9 (L1062–1066) as printed, for squarefree `1 < n ≡ 1, 3 (mod 8)`, `n ≠ 3`, for real
`𝓛`.** For every admissible embedding `τ` (L527–534), every test vector `f_n` (a `ℤ`-generator of
`π_ℤ^{U_n}`, L550) and every real sign choice `ℓ` of `𝓛` on the squarefree classes `1, 3 (mod 8)`
(`ℓ(m)² = 𝓛(m)²`, `lcalSq`, TYZ L336–353), there are signs `ε = ±1` with
`Σ_{n = d₁d₂} ε(d₁, d₂)𝓛(d₁)𝓛(d₂) = Q(n)`, over the non-ordered decompositions `n = d₁d₂`, `d₂ ≡ 1 (mod 8)`
(`pairIdx n`), `Q(n) = Σ_{t ∈ 2Cl_n} f_n(t)` (L566–568, `genusPeriodTV`).

This is `H29Split.TYZLemma29PrintedNe3` (same restrictions of the print: odd classes, `n > 1`, `n ≠ 3`, where
the print is false) with `ℓ : ℕ → ℝ` in place of `ℓ : ℕ → ℤ`. TYZ's `𝓛(m)` is real (L338–353), so a real `ℓ`
with `ℓ(m)² = 𝓛(m)²` is `±𝓛(m)` and the sign is absorbed by `ε`: this is the print. (A real `ℓ` exists:
`lcalSq m ≥ 0`, e.g. by Tunnell's formula, `isLcalSignR_ellR`.) -/
def TYZLemma29PrintedNe3R : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → n ≠ 3 → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVector n τ f →
      ∀ ℓ : ℕ → ℝ, IsLcalSignR ℓ →
        ∃ ε : ℕ → ℤ, (∀ d, ε d = 1 ∨ ε d = -1) ∧
          ∑ d ∈ pairIdx n, (ε d : ℝ) * (ℓ (n / d) * ℓ d) = (genusPeriodTV n τ f : ℝ)

/-! ## §2. Glue: the real form gives the integer form -/

/-- **The real form of Lemma 2.9 gives the open leaf `TYZLemma29PrintedNe3`** (an integer sign choice is a
real one). -/
theorem tyzLemma29PrintedNe3_of_R (h : TYZLemma29PrintedNe3R) : TYZLemma29PrintedNe3 := by
  intro n _ hsq h1 h3 hcl τ hτ f hf ℓ hℓ
  obtain ⟨ε, hε, heq⟩ := h n hsq h1 h3 hcl τ hτ f hf (fun m => (ℓ m : ℝ))
    (fun m hm hc => by simpa using hℓ m hm hc)
  exact ⟨ε, hε, by exact_mod_cast heq⟩

/-! ## §3. Glue: Tunnell's formula at `n = 1, 3`, and Tunnell's sign choice -/

theorem card_eq_of_iff {P : ℤ × ℤ × ℤ → Prop} (s : Finset (ℤ × ℤ × ℤ)) (h : ∀ v, P v ↔ v ∈ s) :
    Nat.card {v // P v} = s.card := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_finsetCard]

theorem tunnellA_one : tunnellA 1 = 2 := by
  unfold tunnellA
  rw [card_eq_of_iff {(0, 1, 0), (0, -1, 0)}]
  · decide
  rintro ⟨x, y, z⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Nat.cast_one]
  constructor
  · intro h
    have hx1 : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg z]
    have hx2 : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg z]
    have hy1 : y ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg z]
    have hy2 : -1 ≤ y := by nlinarith [sq_nonneg x, sq_nonneg z]
    have hz1 : z ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hz2 : -1 ≤ z := by nlinarith [sq_nonneg x, sq_nonneg y]
    interval_cases x <;> interval_cases y <;> interval_cases z <;> simp_all
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num

theorem tunnellB_one : tunnellB 1 = 2 := by
  unfold tunnellB
  rw [card_eq_of_iff {(0, 1, 0), (0, -1, 0)}]
  · decide
  rintro ⟨x, y, z⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Nat.cast_one]
  constructor
  · intro h
    have hx1 : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg z]
    have hx2 : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg z]
    have hy1 : y ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg z]
    have hy2 : -1 ≤ y := by nlinarith [sq_nonneg x, sq_nonneg z]
    have hz1 : z ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hz2 : -1 ≤ z := by nlinarith [sq_nonneg x, sq_nonneg y]
    interval_cases x <;> interval_cases y <;> interval_cases z <;> simp_all
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num

theorem tunnellA_three : tunnellA 3 = 4 := by
  unfold tunnellA
  rw [card_eq_of_iff {(1, 1, 0), (1, -1, 0), (-1, 1, 0), (-1, -1, 0)}]
  · decide
  rintro ⟨x, y, z⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · intro h
    push_cast at h
    have hx1 : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg z]
    have hx2 : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg z]
    have hy1 : y ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg z]
    have hy2 : -1 ≤ y := by nlinarith [sq_nonneg x, sq_nonneg z]
    have hz1 : z ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hz2 : -1 ≤ z := by nlinarith [sq_nonneg x, sq_nonneg y]
    interval_cases x <;> interval_cases y <;> interval_cases z <;> simp_all
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num

theorem tunnellB_three : tunnellB 3 = 4 := by
  unfold tunnellB
  rw [card_eq_of_iff {(1, 1, 0), (1, -1, 0), (-1, 1, 0), (-1, -1, 0)}]
  · decide
  rintro ⟨x, y, z⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · intro h
    push_cast at h
    have hx1 : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg z]
    have hx2 : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg z]
    have hy1 : y ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg z]
    have hy2 : -1 ≤ y := by nlinarith [sq_nonneg x, sq_nonneg z]
    have hz1 : z ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hz2 : -1 ≤ z := by nlinarith [sq_nonneg x, sq_nonneg y]
    interval_cases x <;> interval_cases y <;> interval_cases z <;> simp_all
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num

/-- **`lcalSq` from Tunnell's formula**: for odd squarefree `m`,
`𝓛(m)² = ((A(m) − 2B(m)) / 2^{k(m)+1})²`. -/
theorem lcalSq_eq_of_tunnell (hT : TunnellOddL1) {m : ℕ} (hodd : Odd m) (hsq : Squarefree m) :
    lcalSq m = ((((tunnellA m : ℝ) - 2 * tunnellB m) / 2 ^ (m.primeFactors.card + 1) : ℝ) : ℂ) ^ 2 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast hsq.ne_zero.bot_lt
  have hs : (Real.sqrt m : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hm).ne'
  have hω : (omegaInt : ℂ) ≠ 0 := by exact_mod_cast omegaInt_pos.ne'
  unfold lcalSq omegaTYZ
  rw [hT m hodd hsq]
  have hz : (2 : ℂ) ^ ((2 * m.primeFactors.card : ℤ) - 3) = 2 ^ (2 * m.primeFactors.card) / 2 ^ 3 := by
    rw [zpow_sub₀ two_ne_zero]
    norm_cast
  rw [hz]
  push_cast
  field_simp
  ring

/-- **Tunnell's sign choice of `𝓛`**: `ℓ(m) = (A(m) − 2B(m)) / 2^{k(m)+1}`. -/
def ellR (m : ℕ) : ℝ := ((tunnellA m : ℝ) - 2 * tunnellB m) / 2 ^ (m.primeFactors.card + 1)

theorem isLcalSignR_ellR (hT : TunnellOddL1) : IsLcalSignR ellR := by
  intro m hsq hcl
  have hodd : Odd m := Nat.odd_iff.mpr (by omega)
  rw [lcalSq_eq_of_tunnell hT hodd hsq, ellR]

theorem ellR_one : ellR 1 = -1 := by
  rw [ellR, tunnellA_one, tunnellB_one]
  norm_num

theorem ellR_three : ellR 3 = -1 := by
  rw [ellR, tunnellA_three, tunnellB_three, Nat.prime_three.primeFactors]
  norm_num

/-- **`𝓛(1)² = 1`** (TYZ L1082, "Since `𝓛(1) = 1`"), from Tunnell's formula at `n = 1`. -/
theorem lcalSq_one_of_tunnell (hT : TunnellOddL1) : lcalSq 1 = 1 := by
  rw [← isLcalSignR_ellR hT 1 squarefree_one (Or.inl rfl), ellR_one]
  norm_num

/-- **`𝓛(3)² = 1`**, from Tunnell's formula at `n = 3`. -/
theorem lcalSq_three_of_tunnell (hT : TunnellOddL1) : lcalSq 3 = 1 := by
  rw [← isLcalSignR_ellR hT 3 Nat.prime_three.squarefree (Or.inr rfl), ellR_three]
  norm_num

/-! ## §4. Glue: TYZ's induction (L1081–1088) -/

theorem exists_int_sum {s : Finset ℕ} {g : ℕ → ℝ} (h : ∀ d ∈ s, ∃ z : ℤ, g d = z) :
    ∃ z : ℤ, ∑ d ∈ s, g d = z := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => ⟨0, by simp⟩) ?_
  intro a s ha ih h
  obtain ⟨z₁, h₁⟩ := h a (Finset.mem_insert_self a s)
  obtain ⟨z₂, h₂⟩ := ih fun d hd => h d (Finset.mem_insert_of_mem hd)
  exact ⟨z₁ + z₂, by rw [Finset.sum_insert ha, h₁, h₂]; push_cast; ring⟩

theorem one_mem_pairIdx {m : ℕ} (hm0 : m ≠ 0) (h1 : 1 < m) : 1 ∈ pairIdx m := by
  simp only [pairIdx, Finset.mem_filter, Nat.mem_divisors]
  exact ⟨⟨one_dvd m, hm0⟩, by simp, fun _ => by simpa using h1⟩

/-- **Tunnell's sign choice is integral on the classes `1, 3`**, by TYZ's induction through Lemma 2.9
(`n ≠ 3`), with `n = 1, 3` from Tunnell's formula. -/
theorem ellR_int (hL : LegendreThreeSquares) (hJ : JonesPallX2Y2Z16) (hfx : TYZTestVectorExists)
    (hL29 : TYZLemma29PrintedNe3R) (hT : TunnellOddL1) :
    ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ∃ z : ℤ, ellR m = z := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hsq hcl
  by_cases hm1 : m = 1
  · subst hm1
    exact ⟨-1, by rw [ellR_one]; norm_num⟩
  by_cases hm3 : m = 3
  · subst hm3
    exact ⟨-1, by rw [ellR_three]; norm_num⟩
  have hm0 : m ≠ 0 := hsq.ne_zero
  have h1m : 1 < m := by omega
  have : NeZero m := ⟨hm0⟩
  obtain ⟨τ, hτ⟩ := tyzTauExists_of_legendreJonesPall (legendreJonesPall_of hL hJ) m hsq hcl
  obtain ⟨f, hf, -⟩ := hfx m hsq h1m hcl τ hτ
  obtain ⟨ε, hε, heq⟩ := hL29 m hsq h1m hm3 hcl τ hτ f hf ellR (isLcalSignR_ellR hT)
  rw [← Finset.add_sum_erase _ _ (one_mem_pairIdx hm0 h1m)] at heq
  obtain ⟨S, hS⟩ : ∃ S : ℤ,
      ∑ d ∈ (pairIdx m).erase 1, (ε d : ℝ) * (ellR (m / d) * ellR d) = S := by
    refine exists_int_sum fun d hd => ?_
    rw [Finset.mem_erase] at hd
    obtain ⟨hd1, hd⟩ := hd
    simp only [pairIdx, Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdm, -⟩, hd8, hdd⟩ := hd
    have hd0 : d ≠ 0 := by rintro rfl; simp at hd8
    have hdle : d ≤ m := Nat.le_of_dvd (by omega) hdm
    have hdlt : d < m := by
      rcases hcl with h | h
      · have := hdd h
        nlinarith
      · rcases hdle.lt_or_eq with h' | h'
        · exact h'
        · omega
    have hqlt : m / d < m := Nat.div_lt_self (by omega) (by omega)
    have hq8 : m / d % 8 = m % 8 := by
      rw [div_mod8_of hdm rfl hd8 (Or.inl rfl)]
      omega
    obtain ⟨z₁, h₁⟩ := ih d hdlt (hsq.squarefree_of_dvd hdm) (Or.inl hd8)
    obtain ⟨z₂, h₂⟩ := ih (m / d) hqlt (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdm))
      (by omega)
    exact ⟨ε d * (z₂ * z₁), by rw [h₁, h₂]; push_cast; ring⟩
  rw [Nat.div_one, hS, ellR_one] at heq
  rcases hε 1 with h | h <;> rw [h] at heq <;> push_cast at heq
  · exact ⟨S - genusPeriodTV m τ f, by push_cast; linarith⟩
  · exact ⟨genusPeriodTV m τ f - S, by push_cast; linarith⟩

/-- **`h11` from printed leaves**: TYZ Theorem 1.1's integrality (`TYZThm11Integral`) from TYZ Lemma 2.9 in
its printed (real) form for `n ≠ 3`, Tunnell's formula, and the existence of TYZ's `τ` (Legendre,
Jones–Pall) and test vector `f_n`. -/
theorem tyzThm11Integral_of_leaves (hL : LegendreThreeSquares) (hJ : JonesPallX2Y2Z16)
    (hfx : TYZTestVectorExists) (hL29 : TYZLemma29PrintedNe3R) (hT : TunnellOddL1) :
    TYZThm11Integral := by
  intro m hsq hcl
  obtain ⟨z, hz⟩ := ellR_int hL hJ hfx hL29 hT m hsq hcl
  refine ⟨z, ?_⟩
  rw [← isLcalSignR_ellR hT m hsq hcl, hz]
  push_cast
  rfl

/-! ## §5. Glue: `h29` without TYZ Theorem 2.1 at `(3, 1)` -/

/-- An integer square root of `1` is `±1`. -/
theorem int_sq_one {a : ℤ} (h : ((a : ℂ)) ^ 2 = 1) : a * a = 1 := by
  have : ((a * a : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by push_cast; rw [← h]; ring
  exact_mod_cast this

open Classical in
/-- The genus period of the chosen `τ`, `f_n`, corrected at `n = 3` to `3 = w_K 𝓛(3)𝓛(1) ε`. -/
def qTun (hτ : TYZTauExists) (hfx : TYZTestVectorExists) (m : ℕ) : ℤ :=
  if m = 3 then 3 else genusPeriod (tvFun hτ hfx) m

/-- **`h29` from five printed leaves**: Legendre, Jones–Pall, the test vector, Lemma 2.9 (`n ≠ 3`),
Proposition 2.3, and Tunnell's formula (for `n = 3`, in place of TYZ Theorem 2.1 at `(3, 1)`). -/
theorem tyzLemma29Mod2_of_tunnell (hL : LegendreThreeSquares) (hJ : JonesPallX2Y2Z16)
    (hfx : TYZTestVectorExists) (hNe3 : TYZLemma29PrintedNe3) (h23 : TYZProp23Printed)
    (hT : TunnellOddL1) : TYZLemma29Mod2 := by
  have hτ := tyzTauExists_of_legendreJonesPall (legendreJonesPall_of hL hJ)
  refine tyzLemma29Mod2_of_printed (Q := qTun hτ hfx) ?_ ?_
  · intro ℓ hℓ m hsq h1 hcl
    by_cases h3 : m = 3
    · subst h3
      have e1 := int_sq_one ((hℓ 1 squarefree_one (Or.inl rfl)).trans (lcalSq_one_of_tunnell hT))
      have e3 := int_sq_one ((hℓ 3 Nat.prime_three.squarefree (Or.inr rfl)).trans
        (lcalSq_three_of_tunnell hT))
      have he : (ℓ 3 * ℓ 1) * (ℓ 3 * ℓ 1) = 1 := by
        calc (ℓ 3 * ℓ 1) * (ℓ 3 * ℓ 1) = (ℓ 3 * ℓ 3) * (ℓ 1 * ℓ 1) := by ring
          _ = 1 := by rw [e1, e3, one_mul]
      refine ⟨fun _ => ℓ 3 * ℓ 1, fun _ => mul_self_eq_one_iff.mp he, ?_⟩
      rw [pairIdx_three_eq, Finset.sum_singleton, Nat.div_one, he]
      simp [qTun, wK]
    · have : NeZero m := ⟨hsq.ne_zero⟩
      have hm : Squarefree m ∧ 1 < m ∧ (m % 8 = 1 ∨ m % 8 = 3) := ⟨hsq, h1, hcl⟩
      obtain ⟨ε, hε, key⟩ := hNe3 m hsq h1 h3 hcl _ (hτ m hsq hcl).choose_spec _
        (hfx m hsq h1 hcl _ (hτ m hsq hcl).choose_spec).choose_spec.1 ℓ hℓ
      have hQ : genusPeriod (tvFun hτ hfx) m = genusPeriodTV m (hτ m hsq hcl).choose
          (hfx m hsq h1 hcl _ (hτ m hsq hcl).choose_spec).choose := by
        rw [genusPeriod_of_ne]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [tvFun, dite_eq_left_of_eq_true (eq_true hm)]
      refine ⟨ε, hε, ?_⟩
      have hw : wK m = 1 := by simp [wK, h3]
      rw [hw, one_mul, key, ← hQ]
      simp [qTun, h3]
  · intro m hsq h1 hcl
    by_cases h3 : m = 3
    · subst h3
      rw [ZInQ.Contrib.TYZLcal.gNat_three]
      simp [qTun]
      decide
    · have hO : Prop23Odd (tvFun hτ hfx) := by
        intro n _ hsq h1 hcl t ht
        have hm : Squarefree n ∧ 1 < n ∧ (n % 8 = 1 ∨ n % 8 = 3) := ⟨hsq, h1, hcl⟩
        simp only [tvFun, dite_eq_left_of_eq_true (eq_true hm)]
        have hf := (hfx n hsq h1 hcl _ (hτ n hsq hcl).choose_spec).choose_spec.1
        exact odd_on_sqClasses hf.1 (h23 n hsq h1 hcl _ (hτ n hsq hcl).choose_spec _ hf) ht
      have := prop23Cong_of_odd hO m hsq h1 hcl
      simpa [qTun, h3] using this

/-- `h29` from the real form of Lemma 2.9 (the form `tyzThm11Integral_of_leaves` uses). -/
theorem tyzLemma29Mod2_of_tunnellR (hL : LegendreThreeSquares) (hJ : JonesPallX2Y2Z16)
    (hfx : TYZTestVectorExists) (hL29 : TYZLemma29PrintedNe3R) (h23 : TYZProp23Printed)
    (hT : TunnellOddL1) : TYZLemma29Mod2 :=
  tyzLemma29Mod2_of_tunnell hL hJ hfx (tyzLemma29PrintedNe3_of_R hL29) h23 hT

end ZInQ.Contrib.TYZDecomp.H11Reduce
