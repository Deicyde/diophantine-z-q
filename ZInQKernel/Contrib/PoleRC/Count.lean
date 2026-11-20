import ZInQKernel.Contrib.PoleRC.QClass

/-!
# The dimension-three count from the local images (`diophantine_zq.tex` lines 1061–1074)

The local images of the Kummer map of `E_ℓ` are stated as five textbook GLUE Props (`LocalReal`,
`LocalTwo`, `LocalThree`, `LocalBad`, `LocalGood`), and `dimThreeCount_of_local` proves the
manuscript's `DimThreeCount` from them: the local conditions of a Selmer class become the
equations of `kmat_forces`, which leave exactly the eight classes
`{1, ℓ, β, ℓ/β} × {(1, 1), (3, −ℓ)}`.
-/

namespace ZInQ.Manuscript.PoleRC

open Matrix

variable {ℓ : ℕ}

open Classical in
/-- The indicator, on the prime support of `ℓ`, of the prime factors of `x`. -/
noncomputable def ind (ℓ : ℕ) (x : ℤ) : Supp ℓ → ZMod 2 :=
  fun i => if (i : ℕ) ∈ x.natAbs.primeFactors then 1 else 0

theorem three_not_mem (h12 : ℓ % 12 = 11) : 3 ∉ ℓ.primeFactors := by
  intro h; have := (Nat.mem_primeFactors.mp h).2.1; omega

open Classical in
/-- **`qcls` at a prime of `ℓ` of a squarefree integer supported on `3` and the primes of `ℓ`.**
`(u_i, δλ_i + σ s_i + Σ_{j ≠ i} K_ij u_j)`, the last sum written `(Ku)_i + K_ii u_i`. -/
theorem qcls_formula (h12 : ℓ % 12 = 11) {x : ℤ} (hx : Squarefree x)
    (hsupp : x.natAbs.primeFactors ⊆ insert 3 ℓ.primeFactors) (i : Supp ℓ) :
    haveI := Fact.mk (supp_prime i)
    qcls i x = (ind ℓ x i, (if 3 ∈ x.natAbs.primeFactors then lam ℓ i else 0) +
      (if x < 0 then sgn ℓ i else 0) + ((Kmat ℓ *ᵥ ind ℓ x) i + Kmat ℓ i i * ind ℓ x i)) := by
  have := Fact.mk (supp_prime i)
  have hi3 : (i : ℕ) ≠ 3 := supp_ne_three (by omega) i
  rw [qcls_eq_sum (i : ℕ) hx]
  have h1 : ∑ p ∈ x.natAbs.primeFactors, qcls i p =
      ∑ p ∈ insert 3 ℓ.primeFactors, (if p ∈ x.natAbs.primeFactors then qcls i p else 0) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsupp]
  rw [h1, Finset.sum_insert (three_not_mem h12), ← Finset.sum_coe_sort ℓ.primeFactors,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h3 : qcls i ((3 : ℕ) : ℤ) = (0, lam ℓ i) :=
    qcls_prime_ne (i : ℕ) 3 Nat.prime_three (Ne.symm hi3)
  have hself : qcls i ((i : ℕ) : ℤ) = (1, 0) := qcls_self i
  have hne : ∀ j ∈ (Finset.univ : Finset (Supp ℓ)).erase i,
      (if (j : ℕ) ∈ x.natAbs.primeFactors then qcls i ((j : ℕ) : ℤ) else 0) =
        (0, Kmat ℓ i j * ind ℓ x j) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hji' : (j : ℕ) ≠ i := fun h => hji (Subtype.ext h)
    rw [qcls_prime_ne (i : ℕ) j (supp_prime j) hji']
    simp only [Kmat, ind, if_neg (Ne.symm hji)]
    split_ifs <;> simp <;> rfl
  rw [Finset.sum_congr rfl hne, h3, hself, qcls_neg_one]
  -- the row sum
  have hrow : (Kmat ℓ *ᵥ ind ℓ x) i + Kmat ℓ i i * ind ℓ x i =
      ∑ j ∈ (Finset.univ : Finset (Supp ℓ)).erase i, Kmat ℓ i j * ind ℓ x j := by
    rw [mulVec, dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_comm,
      ← add_assoc, zmod2_add_self, zero_add]
  rw [hrow]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum]
    unfold ind
    split_ifs <;> simp
  · split_ifs <;> simp only [Prod.snd_add, Prod.snd_sum, Prod.snd_zero, sgn, add_zero,
      zero_add] <;> ring

/-! ### The local images of the Kummer map of `E_ℓ` (GLUE, textbook local computations) -/

/-- **Local image at the real place**: for `ℓ > 0`, the class `(a, b)` is in the real Kummer image
iff `a > 0` (real points have `x ≥ ℓ`, giving `a, b > 0`, or `−3ℓ ≤ x ≤ 0`, giving `a > 0 > b`).
Proved in Lean below (`localReal`). -/
def LocalReal : Prop :=
  ∀ (ℓ : ℕ) (a b : ℤ), 0 < ℓ → a ≠ 0 → b ≠ 0 → (LocM ℝ ℓ a b ↔ 0 < a)

/-- **Local image at `2`** (GLUE, textbook): for squarefree `ℓ ≡ 3 (mod 4)` and squarefree
`a, b`, the class `(a, b)` is in the Kummer image of `E_ℓ(ℚ₂)` iff `a, b` are odd and
`b ≡ 1 (mod 4)`. The image has `8 = 2 · #E_ℓ(ℚ₂)[2]` elements. Checked numerically
(`scratch/pc-from-rc/local2.py`, `localprops.py`); not proved in Lean. -/
def LocalTwo : Prop :=
  ∀ (ℓ : ℕ) (a b : ℤ), Squarefree ℓ → ℓ % 4 = 3 → Squarefree a → Squarefree b →
    (LocM ℚ_[2] ℓ a b ↔ a % 2 = 1 ∧ b % 4 = 1)

/-- **Local image at `3`** (GLUE, textbook): for squarefree `ℓ ≡ 2 (mod 3)` (split multiplicative
reduction at `3`), the class `(a, b)` is in the Kummer image of `E_ℓ(ℚ₃)` iff `b ≡ 1 (mod 3)`; the
image is spanned by the torsion classes `(ℓ, 1)`, `(3, −ℓ)`. Checked numerically; not proved in
Lean. -/
def LocalThree : Prop :=
  ∀ (ℓ : ℕ) (a b : ℤ), Squarefree ℓ → ℓ % 3 = 2 → Squarefree a → Squarefree b →
    (LocM ℚ_[3] ℓ a b ↔ b % 3 = 1)

/-- **Local image at a prime `q ∣ ℓ`, `q ≠ 2, 3`** (GLUE, textbook): `E_ℓ` is the quadratic twist
by `ℓ` of a curve with good reduction at `q`, so it has reduction type `I₀*` there, and the
Kummer image of `E_ℓ(ℚ_q)` is spanned by the images `(ℓ, 1)`, `(3, −ℓ)` of the two-torsion
points. In square classes at `q` (`qcls`): `(a, b) = e₁ (ℓ, 1) + e₂ (3, −ℓ)`. Checked numerically;
not proved in Lean. -/
def LocalBad : Prop :=
  ∀ (ℓ q : ℕ) [Fact q.Prime] (a b : ℤ), Squarefree ℓ → q ∣ ℓ → q ≠ 2 → q ≠ 3 →
    Squarefree a → Squarefree b →
    (LocM ℚ_[q] ℓ a b ↔ ∃ e₁ e₂ : ZMod 2,
      qcls q a = e₁ • qcls q ℓ + e₂ • qcls q 3 ∧ qcls q b = e₂ • qcls q (-(ℓ : ℤ)))

/-- **Local image at a prime of good reduction** (GLUE, textbook; Silverman X.4): for `p ∤ 6ℓ`, the
Kummer image of `E_ℓ(ℚ_p)` is the unramified classes: `p ∤ a` and `p ∤ b`. Checked numerically;
not proved in Lean. -/
def LocalGood : Prop :=
  ∀ (ℓ p : ℕ) [Fact p.Prime] (a b : ℤ), Squarefree ℓ → ¬ p ∣ 6 * ℓ →
    Squarefree a → Squarefree b → (LocM ℚ_[p] ℓ a b ↔ ¬ (p : ℤ) ∣ a ∧ ¬ (p : ℤ) ∣ b)

theorem isSquare_real_of_nonneg {r : ℝ} (h : 0 ≤ r) : IsSquare r :=
  ⟨Real.sqrt r, (Real.mul_self_sqrt h).symm⟩

/-- **`LocalReal` holds.** -/
theorem localReal : LocalReal := by
  intro ℓ a b hℓ ha hb
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  constructor
  · rintro (⟨h1, -⟩ | ⟨x, h1, h2, h3⟩)
    · have : (0 : ℝ) ≤ a := h1.nonneg
      have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
      exact_mod_cast lt_of_le_of_ne this (Ne.symm ha')
    · by_contra hneg
      have ha' : (a : ℝ) < 0 := by
        have : a < 0 := lt_of_le_of_ne (not_lt.mp hneg) ha
        exact_mod_cast this
      have e1 := h1.nonneg
      have hx : x + 3 * ℓ ≤ 0 := by
        by_contra hc
        push Not at hc
        have : (x + 3 * ℓ) / (a : ℝ) < 0 := div_neg_of_pos_of_neg hc ha'
        linarith
      have e2 := h2.nonneg
      have hb' : (b : ℝ) < 0 := by
        rcases lt_or_gt_of_ne (show (b : ℝ) ≠ 0 by exact_mod_cast hb) with h | h
        · exact h
        · have : (x - ℓ) / (b : ℝ) < 0 := div_neg_of_neg_of_pos (by linarith) h
          linarith
      have e3 := h3.nonneg
      have : x / ((a : ℝ) * b) < 0 := div_neg_of_neg_of_pos (by linarith) (mul_pos_of_neg_of_neg ha' hb')
      linarith
  · intro ha0
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha0
    rcases lt_or_gt_of_ne (show (b : ℝ) ≠ 0 by exact_mod_cast hb) with hb' | hb'
    · right
      refine ⟨-ℓ, isSquare_real_of_nonneg ?_, isSquare_real_of_nonneg ?_,
        isSquare_real_of_nonneg ?_⟩
      · exact div_nonneg (by linarith) ha'.le
      · exact div_nonneg_of_nonpos (by linarith) hb'.le
      · exact div_nonneg_of_nonpos (by linarith) (mul_neg_of_pos_of_neg ha' hb').le
    · left
      exact ⟨isSquare_real_of_nonneg ha'.le, isSquare_real_of_nonneg hb'.le⟩

/-! ### Square classes of `ℓ`, `3`, `−ℓ` at the primes of `ℓ` -/

theorem natAbs_primeFactors_ell : ((ℓ : ℤ)).natAbs.primeFactors = ℓ.primeFactors := by
  simp

theorem natAbs_primeFactors_negell : (-(ℓ : ℤ)).natAbs.primeFactors = ℓ.primeFactors := by
  simp

theorem ind_ell : ind ℓ (ℓ : ℤ) = 1 := by
  funext i; simp [ind, natAbs_primeFactors_ell, i.2]

theorem ind_negell : ind ℓ (-(ℓ : ℤ)) = 1 := by
  funext i; simp [ind, i.2]

theorem qcls_three (i : Supp ℓ) (h12 : ℓ % 12 = 11) :
    haveI := Fact.mk (supp_prime i)
    qcls i 3 = (0, lam ℓ i) := by
  have := Fact.mk (supp_prime i)
  have h := qcls_prime_ne (i : ℕ) 3 Nat.prime_three (Ne.symm (supp_ne_three (by omega) i))
  simpa [lam] using h

theorem qcls_ell (i : Supp ℓ) (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) :
    haveI := Fact.mk (supp_prime i)
    qcls i (ℓ : ℤ) = (1, Kmat ℓ i i) := by
  have := Fact.mk (supp_prime i)
  rw [qcls_formula h12 (Int.squarefree_natCast.mpr hsf)
    (by rw [natAbs_primeFactors_ell]; exact Finset.subset_insert _ _) i]
  rw [ind_ell, kmat_mulVec_one, natAbs_primeFactors_ell, if_neg (three_not_mem h12),
    if_neg (by simp)]
  simp

theorem qcls_negell (i : Supp ℓ) (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) :
    haveI := Fact.mk (supp_prime i)
    qcls i (-(ℓ : ℤ)) = (1, sgn ℓ i + Kmat ℓ i i) := by
  have := Fact.mk (supp_prime i)
  have hsq : Squarefree (-(ℓ : ℤ)) := by
    rw [← Int.squarefree_natAbs]; simpa using hsf
  have hpos : (0 : ℤ) < ℓ := by have : 0 < ℓ := by omega
                                exact_mod_cast this
  rw [qcls_formula h12 hsq (by rw [natAbs_primeFactors_negell]; exact Finset.subset_insert _ _) i]
  rw [ind_negell, kmat_mulVec_one, natAbs_primeFactors_negell, if_neg (three_not_mem h12),
    if_pos (by omega)]
  simp

/-! ### `𝔽₂` bookkeeping -/

theorem alg_a : ∀ (u Ku Kii lam v δ e1 e2 : ZMod 2), u = e1 → v = e2 →
    δ * lam + 0 + (Ku + Kii * u) = e1 * Kii + e2 * lam → Ku + lam * v = δ * lam := by decide

theorem alg_a' : ∀ (u Ku Kii lam v δ : ZMod 2), Ku + lam * v = δ * lam →
    δ * lam + 0 + (Ku + Kii * u) = u * Kii + v * lam := by decide

theorem alg_b : ∀ (v Kv Kii s σ e2 : ZMod 2), v = e2 →
    0 + σ * s + (Kv + Kii * v) = e2 * (s + Kii) → Kv + s * v = σ * s := by decide

theorem alg_b' : ∀ (v Kv Kii s σ : ZMod 2), Kv + s * v = σ * s →
    0 + σ * s + (Kv + Kii * v) = v * (s + Kii) := by decide

theorem ite_mul_eq (P : Prop) [Decidable P] (x : ZMod 2) :
    (if P then x else 0) = (if P then 1 else 0) * x := by
  split_ifs <;> simp

open Classical in
/-- `δ(a) = 1` iff `3 ∣ a`. -/
noncomputable def dlt (a : ℤ) : ZMod 2 := if 3 ∈ a.natAbs.primeFactors then 1 else 0

open Classical in
/-- `σ(b) = 1` iff `b < 0`. -/
noncomputable def sg (b : ℤ) : ZMod 2 := if b < 0 then 1 else 0

/-- **The local conditions at the primes of `ℓ` give `E1` and `E2`** (lines 1063–1066). -/
theorem eqs_of_localBad (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) {a b : ℤ}
    (ha : Squarefree a) (hb : Squarefree b) (ha0 : 0 < a)
    (hsa : a.natAbs.primeFactors ⊆ insert 3 ℓ.primeFactors)
    (hsb : b.natAbs.primeFactors ⊆ ℓ.primeFactors)
    (hcls : ∀ i : Supp ℓ, ∃ e₁ e₂ : ZMod 2, qcls i a = e₁ • qcls i ℓ + e₂ • qcls i 3 ∧
      qcls i b = e₂ • qcls i (-(ℓ : ℤ))) :
    Kmat ℓ *ᵥ ind ℓ a + lam ℓ * ind ℓ b = dlt a • lam ℓ ∧
      Kmat ℓ *ᵥ ind ℓ b + sgn ℓ * ind ℓ b = sg b • sgn ℓ := by
  have hsb' : b.natAbs.primeFactors ⊆ insert 3 ℓ.primeFactors :=
    hsb.trans (Finset.subset_insert _ _)
  have h3b : 3 ∉ b.natAbs.primeFactors := fun h => three_not_mem h12 (hsb h)
  have key : ∀ i : Supp ℓ, ∃ e₁ e₂ : ZMod 2, ind ℓ a i = e₁ ∧ ind ℓ b i = e₂ ∧
      dlt a * lam ℓ i + 0 + ((Kmat ℓ *ᵥ ind ℓ a) i + Kmat ℓ i i * ind ℓ a i) =
        e₁ * Kmat ℓ i i + e₂ * lam ℓ i ∧
      0 + sg b * sgn ℓ i + ((Kmat ℓ *ᵥ ind ℓ b) i + Kmat ℓ i i * ind ℓ b i) =
        e₂ * (sgn ℓ i + Kmat ℓ i i) := by
    intro i
    have := Fact.mk (supp_prime i)
    obtain ⟨e₁, e₂, h1, h2⟩ := hcls i
    rw [qcls_formula h12 ha hsa i, qcls_ell i hsf h12, qcls_three i h12] at h1
    rw [qcls_formula h12 hb hsb' i, qcls_negell i hsf h12] at h2
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, mul_one, mul_zero, add_zero] at h1 h2
    refine ⟨e₁, e₂, h1.1, h2.1, ?_, ?_⟩
    · rw [← h1.2, if_neg (not_lt.mpr ha0.le), dlt]; split_ifs <;> simp
    · rw [← h2.2, if_neg h3b, sg]; split_ifs <;> simp
  constructor
  · funext i
    obtain ⟨e₁, e₂, hu, hv, hA, -⟩ := key i
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    exact alg_a _ _ _ _ _ _ e₁ e₂ hu hv hA
  · funext i
    obtain ⟨e₁, e₂, -, hv, -, hB⟩ := key i
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    exact alg_b _ _ _ _ _ e₂ hv hB

/-! ### The conditions at two and three: `E3` and `E4` -/

theorem prod_zmod4 (T : Finset ℕ) (hT : ∀ p ∈ T, p % 2 = 1) :
    ((∏ p ∈ T, p : ℕ) : ZMod 4) = (-1) ^ (T.filter (fun p => p % 4 = 3)).card := by
  have hq : ∀ q ∈ T, (q : ZMod 4) = if q % 4 = 3 then -1 else 1 := by
    intro q hq
    rw [← ZMod.natCast_mod q 4]
    have : q % 4 = 1 ∨ q % 4 = 3 := by have := hT q hq; omega
    rcases this with h | h <;> rw [h] <;> decide
  push_cast
  rw [Finset.prod_congr rfl hq, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

theorem prod_zmod3 (T : Finset ℕ) (hT : ∀ p ∈ T, p % 3 ≠ 0) :
    ((∏ p ∈ T, p : ℕ) : ZMod 3) = (-1) ^ (T.filter (fun p => p % 3 = 2)).card := by
  have hq : ∀ q ∈ T, (q : ZMod 3) = if q % 3 = 2 then -1 else 1 := by
    intro q hq
    rw [← ZMod.natCast_mod q 3]
    have : q % 3 = 1 ∨ q % 3 = 2 := by have := hT q hq; omega
    rcases this with h | h <;> rw [h] <;> decide
  push_cast
  rw [Finset.prod_congr rfl hq, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

theorem dot_ind_eq_card (f : ℕ → Prop) [DecidablePred f] {b : ℤ}
    (hsb : b.natAbs.primeFactors ⊆ ℓ.primeFactors) :
    ∑ i : Supp ℓ, (if f i then (1 : ZMod 2) else 0) * ind ℓ b i =
      ((b.natAbs.primeFactors.filter f).card : ZMod 2) := by
  classical
  have h : ∀ i : Supp ℓ, (if f i then (1 : ZMod 2) else 0) * ind ℓ b i =
      if (i : ℕ) ∈ b.natAbs.primeFactors then (if f i then 1 else 0) else 0 := by
    intro i; simp only [ind]; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun i _ => h i),
    sum_supp_eq (fun q => if q ∈ b.natAbs.primeFactors then (if f q then (1 : ZMod 2) else 0)
      else 0), Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsb, Finset.sum_boole]

theorem natAbs_eq_prod {b : ℤ} (hb : Squarefree b) :
    b.natAbs = ∏ p ∈ b.natAbs.primeFactors, p :=
  (Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hb)).symm

theorem intCast_eq_sign_mul (R : Type*) [CommRing R] (b : ℤ) :
    (b : R) = (if b < 0 then -1 else 1) * ((b.natAbs : ℕ) : R) := by
  by_cases h : b < 0
  · rw [if_pos h]
    have : b = -(b.natAbs : ℤ) := by rw [Int.natCast_natAbs, abs_of_neg h]; ring
    conv_lhs => rw [this]
    rw [Int.cast_neg, Int.cast_natCast]; ring
  · rw [if_neg h, one_mul]
    have : b = (b.natAbs : ℤ) := by rw [Int.natCast_natAbs, abs_of_nonneg (not_lt.mp h)]
    conv_lhs => rw [this]
    rw [Int.cast_natCast]

theorem even_of_neg_one_pow {R : Type*} [Ring R] (h : (-1 : R) ≠ 1) {n : ℕ}
    (hn : (-1 : R) ^ n = 1) : Even n := by
  rcases Nat.even_or_odd n with he | ho
  · exact he
  · rw [ho.neg_one_pow] at hn; exact absurd hn h

theorem zmod2_eq_of_even {σ c : ℕ} (h : Even (σ + c)) : (c : ZMod 2) = σ := by
  have : ((σ + c : ℕ) : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff_even).mpr h
  push_cast at this
  have key : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
  exact key _ _ this

theorem sg_eq_cast (b : ℤ) : sg b = ((if b < 0 then 1 else 0 : ℕ) : ZMod 2) := by
  unfold sg; split_ifs <;> simp

/-- **`E3`: the condition at two** (`b ≡ 1 (mod 4)` gives `sᵗv = σ`). -/
theorem e3_of_mod4 (h12 : ℓ % 12 = 11) {b : ℤ} (hb : Squarefree b)
    (hsb : b.natAbs.primeFactors ⊆ ℓ.primeFactors) (h4 : b % 4 = 1) :
    sgn ℓ ⬝ᵥ ind ℓ b = sg b := by
  classical
  have hT : ∀ p ∈ b.natAbs.primeFactors, p % 2 = 1 := fun p hp =>
    supp_mod_two (ℓ := ℓ) (by omega) ⟨p, hsb hp⟩
  have hZ := intCast_eq_sign_mul (ZMod 4) b
  rw [natAbs_eq_prod hb, prod_zmod4 _ hT] at hZ
  have hb1 : (b : ZMod 4) = 1 := by
    rw [← ZMod.intCast_mod b 4, show b % ((4 : ℕ) : ℤ) = 1 by simpa using h4]; rfl
  rw [hb1] at hZ
  have hpar : Even ((if b < 0 then 1 else 0) +
      (b.natAbs.primeFactors.filter (fun p => p % 4 = 3)).card) := by
    apply even_of_neg_one_pow (R := ZMod 4) (by decide)
    rw [pow_add, show ((-1 : ZMod 4) ^ (if b < 0 then 1 else 0)) = (if b < 0 then -1 else 1) by
      split_ifs <;> simp]
    exact hZ.symm
  have hdot : sgn ℓ ⬝ᵥ ind ℓ b = ((b.natAbs.primeFactors.filter (fun p => p % 4 = 3)).card :
      ZMod 2) := by
    rw [dotProduct, ← dot_ind_eq_card (fun p => p % 4 = 3) hsb]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Fact.mk (supp_prime i)
    rw [sgn, lsym_neg_one]
  rw [hdot, sg_eq_cast]
  exact zmod2_eq_of_even hpar

/-- **`E4`: the condition at three** (`b ≡ 1 (mod 3)` gives `(λ + s)ᵗv = σ`). -/
theorem e4_of_mod3 (h12 : ℓ % 12 = 11) {b : ℤ} (hb : Squarefree b)
    (hsb : b.natAbs.primeFactors ⊆ ℓ.primeFactors) (h3 : b % 3 = 1) :
    (lam ℓ + sgn ℓ) ⬝ᵥ ind ℓ b = sg b := by
  classical
  have hT : ∀ p ∈ b.natAbs.primeFactors, p % 3 ≠ 0 := by
    intro p hp h
    have hp3 := supp_ne_three (ℓ := ℓ) (by omega) ⟨p, hsb hp⟩
    have hpp := (Nat.mem_primeFactors.mp hp).1
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp
      (Nat.dvd_of_mod_eq_zero h)).symm
  have hZ := intCast_eq_sign_mul (ZMod 3) b
  rw [natAbs_eq_prod hb, prod_zmod3 _ hT] at hZ
  have hb1 : (b : ZMod 3) = 1 := by
    rw [← ZMod.intCast_mod b 3, show b % ((3 : ℕ) : ℤ) = 1 by simpa using h3]; rfl
  rw [hb1] at hZ
  have hpar : Even ((if b < 0 then 1 else 0) +
      (b.natAbs.primeFactors.filter (fun p => p % 3 = 2)).card) := by
    apply even_of_neg_one_pow (R := ZMod 3) (by decide)
    rw [pow_add, show ((-1 : ZMod 3) ^ (if b < 0 then 1 else 0)) = (if b < 0 then -1 else 1) by
      split_ifs <;> simp]
    exact hZ.symm
  have hdot : (lam ℓ + sgn ℓ) ⬝ᵥ ind ℓ b =
      ((b.natAbs.primeFactors.filter (fun p => p % 3 = 2)).card : ZMod 2) := by
    rw [dotProduct, ← dot_ind_eq_card (fun p => p % 3 = 2) hsb]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Fact.mk (supp_prime i)
    rw [Pi.add_apply, lam, sgn, lsym_three i (supp_mod_two (by omega) i)
      (supp_ne_three (by omega) i), lsym_neg_one, add_assoc, zmod2_add_self, add_zero]
  rw [hdot, sg_eq_cast]
  exact zmod2_eq_of_even hpar

/-! ### Necessity: a Selmer class gives a solution of the local equations -/

theorem prime_dvd_six_mul {p : ℕ} (hp : p.Prime) (h : p ∣ 6 * ℓ) :
    p = 2 ∨ p = 3 ∨ p ∣ ℓ := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h6 | hl
  · rw [show (6 : ℕ) = 2 * 3 by norm_num] at h6
    rcases (Nat.Prime.dvd_mul hp).mp h6 with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3))
  · exact Or.inr (Or.inr hl)

/-- The "only if" halves of the local images, at every class of `SelM ℓ`. -/
def NecAt (ℓ : ℕ) : Prop :=
  ∀ a b : ℤ, (a, b) ∈ SelM ℓ → (a % 2 = 1 ∧ b % 4 = 1) ∧ b % 3 = 1 ∧
    (∀ p : ℕ, p.Prime → ¬ p ∣ 6 * ℓ → ¬ (p : ℤ) ∣ a ∧ ¬ (p : ℤ) ∣ b) ∧
    (∀ i : Supp ℓ, ∃ e₁ e₂ : ZMod 2, qcls i a = e₁ • qcls i ℓ + e₂ • qcls i 3 ∧
      qcls i b = e₂ • qcls i (-(ℓ : ℤ)))

theorem necAt_of_local (hTwo : LocalTwo) (hThree : LocalThree) (hq : LocalBad)
    (hg : LocalGood) (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) : NecAt ℓ := by
  intro a b hab
  obtain ⟨ha, hb, -, hp⟩ := hab
  simp only at ha hb hp
  refine ⟨(hTwo ℓ a b hsf (by omega) ha hb).mp (hp 2),
    (hThree ℓ a b hsf (by omega) ha hb).mp (hp 3), fun p hpp hnd => ?_, fun i => ?_⟩
  · have := Fact.mk hpp
    exact (hg ℓ p a b hsf hnd ha hb).mp (hp p)
  · have := Fact.mk (supp_prime i)
    exact (hq ℓ i a b hsf (supp_dvd i)
      (by have := supp_mod_two (ℓ := ℓ) (by omega) i; omega) (supp_ne_three (by omega) i)
      ha hb).mp (hp i)

theorem sel_necessary (hN : NecAt ℓ) {β : ℕ} (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11)
    (hM : MatrixConditions ℓ β) {a b : ℤ} (hab : (a, b) ∈ SelM ℓ) :
    0 < a ∧ a.natAbs.primeFactors ⊆ insert 3 ℓ.primeFactors ∧
      b.natAbs.primeFactors ⊆ ℓ.primeFactors ∧
      ind ℓ b = sg b • 1 ∧ dlt a = sg b ∧ Kmat ℓ *ᵥ ind ℓ a = 0 := by
  obtain ⟨⟨ha2, hb4⟩, hb3, hgood, hcls⟩ := hN a b hab
  obtain ⟨ha, hb, hR, -⟩ := hab
  simp only at ha hb hR
  have hℓ : 0 < ℓ := by omega
  have ha0 : 0 < a := (localReal ℓ a b hℓ ha.ne_zero hb.ne_zero).mp hR
  have hsupp : ∀ x : ℤ, x % 2 = 1 → (∀ p : ℕ, p.Prime → ¬ p ∣ 6 * ℓ → ¬ (p : ℤ) ∣ x) →
      x.natAbs.primeFactors ⊆ insert 3 ℓ.primeFactors := by
    intro x hx2 hxg p hpx
    have hpp := (Nat.mem_primeFactors.mp hpx).1
    have hpd : (p : ℤ) ∣ x := Int.natCast_dvd.mpr (Nat.mem_primeFactors.mp hpx).2.1
    by_cases h6 : p ∣ 6 * ℓ
    · rcases prime_dvd_six_mul hpp h6 with h | h | h
      · subst h; omega
      · subst h; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Nat.mem_primeFactors.mpr ⟨hpp, h, by omega⟩)
    · exact absurd hpd (hxg p hpp h6)
  have hsa := hsupp a ha2 (fun p hpp hnd => (hgood p hpp hnd).1)
  have hsb : b.natAbs.primeFactors ⊆ ℓ.primeFactors := by
    intro p hpx
    rcases Finset.mem_insert.mp (hsupp b (by omega) (fun p hpp hnd => (hgood p hpp hnd).2) hpx)
      with h | h
    · subst h
      have : (3 : ℤ) ∣ b := Int.natCast_dvd.mpr (Nat.mem_primeFactors.mp hpx).2.1
      omega
    · exact h
  obtain ⟨E1, E2⟩ := eqs_of_localBad hsf h12 ha hb ha0 hsa hsb hcls
  have E3 := e3_of_mod4 h12 hb hsb hb4
  have E4 := e4_of_mod3 h12 hb hsb hb3
  obtain ⟨h1, h2, h3⟩ := kmat_forces hsf h12 hM (ind ℓ a) (ind ℓ b) (dlt a) (sg b) E1 E2 E3 E4
  exact ⟨ha0, hsa, hsb, h1, h2, h3⟩

/-! ### A squarefree integer is determined by its sign and its prime factors -/

theorem eq_of_primeFactors {x y : ℤ} (hx : Squarefree x) (hy : Squarefree y)
    (hpf : x.natAbs.primeFactors = y.natAbs.primeFactors) (hs : x < 0 ↔ y < 0) : x = y := by
  have hn : x.natAbs = y.natAbs := by rw [natAbs_eq_prod hx, natAbs_eq_prod hy, hpf]
  have ex := intCast_eq_sign_mul ℤ x
  have ey := intCast_eq_sign_mul ℤ y
  simp only [Int.cast_id] at ex ey
  rw [ex, ey, hn]
  by_cases h : x < 0
  · rw [if_pos h, if_pos (hs.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hs.mpr h'))]

theorem primeFactors_eq_of_ind {x y : ℤ} (hx : x.natAbs.primeFactors ⊆ insert 3 ℓ.primeFactors)
    (hy : y.natAbs.primeFactors ⊆ insert 3 ℓ.primeFactors) (hd : dlt x = dlt y)
    (hi : ind ℓ x = ind ℓ y) : x.natAbs.primeFactors = y.natAbs.primeFactors := by
  classical
  have key : ∀ z : ℤ, z.natAbs.primeFactors ⊆ insert 3 ℓ.primeFactors → ∀ p : ℕ,
      p ∈ z.natAbs.primeFactors ↔ (p = 3 ∧ dlt z = 1) ∨
        (∃ h : p ∈ ℓ.primeFactors, ind ℓ z ⟨p, h⟩ = 1) := by
    intro z hz p
    constructor
    · intro hp
      rcases Finset.mem_insert.mp (hz hp) with h | h
      · subst h; left; exact ⟨rfl, by simp [dlt, hp]⟩
      · right; exact ⟨h, by simp [ind, hp]⟩
    · rintro (⟨rfl, h⟩ | ⟨h, h'⟩)
      · by_contra hc; simp [dlt, hc] at h
      · by_contra hc; simp [ind, hc] at h'
  ext p
  rw [key x hx p, key y hy p, hd, hi]

theorem ind_eq_of_smul {x : ℤ} (hx : x.natAbs.primeFactors ⊆ ℓ.primeFactors) :
    x.natAbs.primeFactors ⊆ insert 3 ℓ.primeFactors := hx.trans (Finset.subset_insert _ _)

theorem dlt_of_subset (h12 : ℓ % 12 = 11) {x : ℤ} (hx : x.natAbs.primeFactors ⊆ ℓ.primeFactors) :
    dlt x = 0 := by
  simp only [dlt]; rw [if_neg (fun h => three_not_mem h12 (hx h))]

/-- **Upper bound data**: on `SelM ℓ`, the map `(a, b) ↦ (ind a, σ(b))` is injective with values in
`ker K × 𝔽₂`. -/
theorem sel_injOn (hN : NecAt ℓ) {β : ℕ} (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) (hM : MatrixConditions ℓ β) :
    Set.InjOn (fun ab : ℤ × ℤ => (ind ℓ ab.1, sg ab.2)) (SelM ℓ) := by
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hia, hsg⟩ := h
  obtain ⟨ha0, hsa, hsb, hvb, hda, -⟩ := sel_necessary hN hsf h12 hM hab
  obtain ⟨ha0', hsa', hsb', hvb', hda', -⟩ := sel_necessary hN hsf h12 hM hab'
  have ha := hab.1
  have hb := hab.2.1
  have ha' := hab'.1
  have hb' := hab'.2.1
  simp only at ha hb ha' hb'
  have e1 : a = a' := eq_of_primeFactors ha ha'
    (primeFactors_eq_of_ind hsa hsa' (by rw [hda, hda', hsg]) hia)
    ⟨fun h => absurd h (not_lt.mpr ha0.le), fun h => absurd h (not_lt.mpr ha0'.le)⟩
  have e2 : b = b' := by
    refine eq_of_primeFactors hb hb' (primeFactors_eq_of_ind (ind_eq_of_smul hsb)
      (ind_eq_of_smul hsb') (by rw [dlt_of_subset h12 hsb, dlt_of_subset h12 hsb'])
      (by rw [hvb, hvb', hsg])) ?_
    have : sg b = sg b' := hsg
    unfold sg at this
    by_cases h1 : b < 0 <;> by_cases h2 : b' < 0
    · exact ⟨fun _ => h2, fun _ => h1⟩
    · rw [if_pos h1, if_neg h2] at this; exact absurd this (by decide)
    · rw [if_neg h1, if_pos h2] at this; exact absurd this (by decide)
    · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  rw [e1, e2]

/-! ### Sufficiency: a solution of the local equations is a Selmer class -/

theorem localBad_of_eqs (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) {a b : ℤ}
    (ha : Squarefree a) (hb : Squarefree b) (ha0 : 0 < a)
    (hsa : a.natAbs.primeFactors ⊆ insert 3 ℓ.primeFactors)
    (hsb : b.natAbs.primeFactors ⊆ ℓ.primeFactors)
    (E1 : Kmat ℓ *ᵥ ind ℓ a + lam ℓ * ind ℓ b = dlt a • lam ℓ)
    (E2 : Kmat ℓ *ᵥ ind ℓ b + sgn ℓ * ind ℓ b = sg b • sgn ℓ) (i : Supp ℓ) :
    ∃ e₁ e₂ : ZMod 2, qcls i a = e₁ • qcls i ℓ + e₂ • qcls i 3 ∧
      qcls i b = e₂ • qcls i (-(ℓ : ℤ)) := by
  have h3b : 3 ∉ b.natAbs.primeFactors := fun h => three_not_mem h12 (hsb h)
  have e1 := congrFun E1 i
  have e2 := congrFun E2 i
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
  refine ⟨ind ℓ a i, ind ℓ b i, ?_, ?_⟩
  · rw [qcls_formula h12 ha hsa i, qcls_ell i hsf h12, qcls_three i h12]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      have := alg_a' (ind ℓ a i) _ (Kmat ℓ i i) _ _ _ e1
      rw [← this, if_neg (not_lt.mpr ha0.le), dlt]
      split_ifs <;> simp
  · rw [qcls_formula h12 hb (hsb.trans (Finset.subset_insert _ _)) i, qcls_negell i hsf h12]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.smul_snd, smul_eq_mul]
      have := alg_b' _ _ (Kmat ℓ i i) _ _ e2
      rw [← this, if_neg h3b, sg]
      split_ifs <;> simp

theorem sel_sufficient (hTwo : LocalTwo) (hThree : LocalThree) (hq : LocalBad) (hg : LocalGood)
    (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) {a b : ℤ}
    (ha : Squarefree a) (hb : Squarefree b) (ha0 : 0 < a) (ha2 : a % 2 = 1) (hb4 : b % 4 = 1)
    (hb3 : b % 3 = 1) (hsa : a.natAbs.primeFactors ⊆ insert 3 ℓ.primeFactors)
    (hsb : b.natAbs.primeFactors ⊆ ℓ.primeFactors)
    (E1 : Kmat ℓ *ᵥ ind ℓ a + lam ℓ * ind ℓ b = dlt a • lam ℓ)
    (E2 : Kmat ℓ *ᵥ ind ℓ b + sgn ℓ * ind ℓ b = sg b • sgn ℓ) : (a, b) ∈ SelM ℓ := by
  have hℓ : 0 < ℓ := by omega
  refine ⟨ha, hb, (localReal ℓ a b hℓ ha.ne_zero hb.ne_zero).mpr ha0, ?_⟩
  intro p hp
  by_cases hp2 : p = 2
  · subst hp2; exact (hTwo ℓ a b hsf (by omega) ha hb).mpr ⟨ha2, hb4⟩
  by_cases hp3 : p = 3
  · subst hp3; exact (hThree ℓ a b hsf (by omega) ha hb).mpr hb3
  by_cases hpl : p ∣ ℓ
  · let i : Supp ℓ := ⟨p, Nat.mem_primeFactors.mpr ⟨hp.out, hpl, by omega⟩⟩
    exact (hq ℓ p a b hsf hpl hp2 hp3 ha hb).mpr
      (localBad_of_eqs hsf h12 ha hb ha0 hsa hsb E1 E2 i)
  · have hnd : ¬ p ∣ 6 * ℓ := fun h => by
      rcases prime_dvd_six_mul hp.out h with h | h | h
      · exact hp2 h
      · exact hp3 h
      · exact hpl h
    refine (hg ℓ p a b hsf hnd ha hb).mpr ⟨fun hpa => ?_, fun hpb => ?_⟩
    · have hmem : p ∈ a.natAbs.primeFactors := Nat.mem_primeFactors.mpr
        ⟨hp.out, Int.natCast_dvd.mp hpa, by have := ha.ne_zero; omega⟩
      rcases Finset.mem_insert.mp (hsa hmem) with h | h
      · exact hp3 h
      · exact hpl (Nat.mem_primeFactors.mp h).2.1
    · have hmem : p ∈ b.natAbs.primeFactors := Nat.mem_primeFactors.mpr
        ⟨hp.out, Int.natCast_dvd.mp hpb, by have := hb.ne_zero; omega⟩
      exact hpl (Nat.mem_primeFactors.mp (hsb hmem)).2.1

/-! ### The eight classes -/

theorem ind_one : ind ℓ 1 = 0 := by funext i; simp [ind]

theorem sg_one : sg 1 = 0 := by simp [sg]

theorem sg_negell (hℓ : 0 < ℓ) : sg (-(ℓ : ℤ)) = 1 := by
  simp only [sg]; rw [if_pos (by omega)]

theorem natAbs_three_mul (c : ℤ) : (3 * c).natAbs = 3 * c.natAbs := by
  rw [Int.natAbs_mul]; rfl

theorem primeFactors_three_mul {c : ℤ} (hc : c ≠ 0) :
    (3 * c).natAbs.primeFactors = insert 3 c.natAbs.primeFactors := by
  rw [natAbs_three_mul, Nat.primeFactors_mul (by norm_num) (by omega),
    Nat.Prime.primeFactors Nat.prime_three]
  rfl

theorem ind_three_mul (h12 : ℓ % 12 = 11) {c : ℤ} (hc : c ≠ 0) : ind ℓ (3 * c) = ind ℓ c := by
  funext i
  simp only [ind, primeFactors_three_mul hc, Finset.mem_insert,
    supp_ne_three (ℓ := ℓ) (by omega) i, false_or]

theorem dlt_three_mul {c : ℤ} (hc : c ≠ 0) : dlt (3 * c) = 1 := by
  simp [dlt, primeFactors_three_mul hc]

theorem squarefree_three_mul (h12 : ℓ % 12 = 11) {c : ℤ} (hc : Squarefree c)
    (hcl : c.natAbs.primeFactors ⊆ ℓ.primeFactors) : Squarefree (3 * c) := by
  rw [← Int.squarefree_natAbs, natAbs_three_mul, Nat.squarefree_mul_iff]
  refine ⟨?_, Nat.prime_three.squarefree, Int.squarefree_natAbs.mpr hc⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h
  exact three_not_mem h12 (hcl (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h,
    by have := hc.ne_zero; omega⟩))

theorem odd_of_subset (h12 : ℓ % 12 = 11) {c : ℤ} (hc : c ≠ 0)
    (hcl : c.natAbs.primeFactors ⊆ ℓ.primeFactors) : c % 2 = 1 := by
  by_contra h
  have h2 : (2 : ℤ) ∣ c := by omega
  have : 2 ∈ ℓ.primeFactors := hcl (Nat.mem_primeFactors.mpr ⟨Nat.prime_two,
    Int.natCast_dvd.mp (by exact_mod_cast h2), by omega⟩)
  have := (Nat.mem_primeFactors.mp this).2.1
  omega

/-- **A class `(3^σ c, (−ℓ)^σ)`** with `c ∣ ℓ` positive and `K ind(c) = 0` lies in `SelM ℓ`. -/
theorem cand_mem (hTwo : LocalTwo) (hThree : LocalThree) (hq : LocalBad) (hg : LocalGood)
    (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) {c : ℤ} (hc : Squarefree c) (hc0 : 0 < c)
    (hcl : c.natAbs.primeFactors ⊆ ℓ.primeFactors) (hK : Kmat ℓ *ᵥ ind ℓ c = 0) (σ : Bool) :
    ((if σ then 3 else 1) * c, if σ then -(ℓ : ℤ) else 1) ∈ SelM ℓ := by
  have hℓ : 0 < ℓ := by omega
  have hc2 := odd_of_subset h12 hc.ne_zero hcl
  cases σ with
  | false =>
    simp only [Bool.false_eq_true, if_false, one_mul]
    refine sel_sufficient hTwo hThree hq hg hsf h12 hc squarefree_one hc0 hc2 rfl rfl
      (hcl.trans (Finset.subset_insert _ _)) (by simp) ?_ ?_
    · rw [ind_one, dlt_of_subset h12 hcl, hK, mul_zero, add_zero, zero_smul]
    · rw [ind_one, sg_one, mulVec_zero, mul_zero, add_zero, zero_smul]
  | true =>
    simp only [if_true]
    have hsq := squarefree_three_mul h12 hc hcl
    have hnl : Squarefree (-(ℓ : ℤ)) := by rw [← Int.squarefree_natAbs]; simpa using hsf
    refine sel_sufficient hTwo hThree hq hg hsf h12 hsq hnl (by omega) (by omega) (by omega)
      (by omega) ?_ (by rw [natAbs_primeFactors_negell]) ?_ ?_
    · rw [primeFactors_three_mul hc.ne_zero]
      exact Finset.insert_subset_insert _ hcl
    · rw [ind_three_mul h12 hc.ne_zero, hK, ind_negell, dlt_three_mul hc.ne_zero, zero_add,
        mul_one, one_smul]
    · rw [ind_negell, sg_negell hℓ, kmat_mulVec_one, mul_one, zero_add, one_smul]

theorem ind_natCast_of_dvd {c : ℕ} (hc : c ≠ 0) :
    ind ℓ (c : ℤ) = fun i : Supp ℓ => if (i : ℕ) ∣ c then (1 : ZMod 2) else 0 := by
  funext i
  simp only [ind, Int.natAbs_natCast]
  have hp := supp_prime i
  by_cases h : (i : ℕ) ∣ c
  · rw [if_pos (Nat.mem_primeFactors.mpr ⟨hp, h, hc⟩), if_pos h]
  · rw [if_neg (fun h' => h (Nat.mem_primeFactors.mp h').2.1), if_neg h]

theorem primeFactors_natCast_subset {c : ℕ} (hcl : c ∣ ℓ) (hℓ : ℓ ≠ 0) :
    (c : ℤ).natAbs.primeFactors ⊆ ℓ.primeFactors := by
  rw [Int.natAbs_natCast]; exact Nat.primeFactors_mono hcl hℓ

theorem vec4_ne {b : Supp ℓ → ZMod 2} (h0 : b ≠ 0) (h1 : b ≠ 1) :
    ((0 : Supp ℓ → ZMod 2) ≠ 1 ∧ (0 : Supp ℓ → ZMod 2) ≠ b ∧ (0 : Supp ℓ → ZMod 2) ≠ 1 + b) ∧
      ((1 : Supp ℓ → ZMod 2) ≠ b ∧ (1 : Supp ℓ → ZMod 2) ≠ 1 + b) ∧ b ≠ 1 + b := by
  have h10 : (1 : Supp ℓ → ZMod 2) ≠ 0 := fun h => h0 (funext fun i =>
    absurd (congrFun h i) one_ne_zero)
  refine ⟨⟨Ne.symm h10, Ne.symm h0, fun h => h1 ?_⟩, ⟨Ne.symm h1, fun h => h0 ?_⟩, fun h => h10 ?_⟩
  · have : b = 1 + b + 1 := by rw [add_comm (1 : Supp ℓ → ZMod 2) b, add_assoc, vec_add_self,
      add_zero]
    rw [this, ← h, zero_add]
  · have : b = 1 + b + 1 := by rw [add_comm (1 : Supp ℓ → ZMod 2) b, add_assoc, vec_add_self,
      add_zero]
    rw [this, ← h, vec_add_self]
  · have : (1 : Supp ℓ → ZMod 2) = 1 + b + b := by rw [add_assoc, vec_add_self, add_zero]
    rw [this, ← h, vec_add_self]

/-- **The dimension-three count from the local images** (lines 1061–1074). -/
theorem dimThreeCount_of_local (hTwo : LocalTwo) (hThree : LocalThree) (hq : LocalBad)
    (hg : LocalGood) : DimThreeCount := by
  classical
  intro ℓ β hℓ hsf h12 hβℓ hβ8 hM
  have hℓ0 : ℓ ≠ 0 := by omega
  have hβ0 : β ≠ 0 := by rintro rfl; rw [zero_dvd_iff] at hβℓ; omega
  obtain ⟨hb0, hb1, hKb, hker, -⟩ := id hM
  -- the four `c`
  have hsfZ : ∀ c : ℕ, c ∣ ℓ → Squarefree (c : ℤ) := fun c hc =>
    Int.squarefree_natCast.mpr (Squarefree.squarefree_of_dvd hc hsf)
  have hposZ : ∀ c : ℕ, c ∣ ℓ → (0 : ℤ) < c := fun c hc => by
    have : 0 < c := Nat.pos_of_dvd_of_pos hc (by omega)
    exact_mod_cast this
  set ℓ' := ℓ / β with hℓ'
  have hℓ'd : ℓ' ∣ ℓ := Nat.div_dvd_of_dvd hβℓ
  have hℓeq : ℓ = β * ℓ' := (Nat.mul_div_cancel' hβℓ).symm
  have hcop : Nat.Coprime β ℓ' := (Nat.squarefree_mul_iff.mp (hℓeq ▸ hsf)).1
  have hindβ : ind ℓ (β : ℤ) = oneB ℓ β := by
    rw [ind_natCast_of_dvd hβ0]; rfl
  have hindℓ' : ind ℓ (ℓ' : ℤ) = 1 + oneB ℓ β := by
    rw [ind_natCast_of_dvd (Nat.pos_of_dvd_of_pos hℓ'd (by omega)).ne']
    funext i
    have hi : (i : ℕ) ∣ β * ℓ' := hℓeq ▸ supp_dvd i
    simp only [Pi.add_apply, Pi.one_apply, oneB]
    by_cases h : (i : ℕ) ∣ β
    · have : ¬ (i : ℕ) ∣ ℓ' := fun h' => (supp_prime i).one_lt.ne'
        ((Nat.Coprime.coprime_dvd_left h hcop).eq_one_of_dvd h')
      rw [if_neg this, if_pos h]; decide
    · have : (i : ℕ) ∣ ℓ' := ((supp_prime i).dvd_mul.mp hi).resolve_left h
      rw [if_pos this, if_neg h]; decide
  have hK1 : Kmat ℓ *ᵥ (1 + oneB ℓ β) = 0 := by
    rw [mulVec_add, kmat_mulVec_one, hKb, add_zero]
  have hind1 : ind ℓ ((1 : ℕ) : ℤ) = 0 := by rw [Nat.cast_one]; exact ind_one
  -- the map and its image
  let T : Finset ((Supp ℓ → ZMod 2) × ZMod 2) :=
    ({0, 1, oneB ℓ β, 1 + oneB ℓ β} : Finset (Supp ℓ → ZMod 2)) ×ˢ ({0, 1} : Finset (ZMod 2))
  have hcand : ∀ c : ℕ, c ∣ ℓ → Kmat ℓ *ᵥ ind ℓ (c : ℤ) = 0 → ∀ σ : Bool,
      ((if σ then 3 else 1) * (c : ℤ), if σ then -(ℓ : ℤ) else 1) ∈ SelM ℓ ∧
        (ind ℓ ((if σ then 3 else 1) * (c : ℤ)), sg (if σ then -(ℓ : ℤ) else 1)) =
          (ind ℓ (c : ℤ), if σ then 1 else 0) := by
    intro c hc hK σ
    refine ⟨cand_mem hTwo hThree hq hg hsf h12 (hsfZ c hc) (hposZ c hc)
      (primeFactors_natCast_subset hc hℓ0) hK σ, ?_⟩
    cases σ with
    | false => simp [sg_one]
    | true =>
      simp only [if_true]
      rw [ind_three_mul h12 (hposZ c hc).ne', sg_negell hℓ]
  have hN := necAt_of_local hTwo hThree hq hg hsf h12
  have himage : (fun ab : ℤ × ℤ => (ind ℓ ab.1, sg ab.2)) '' SelM ℓ = ↑T := by
    ext ⟨u, σ⟩
    simp only [T, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨a, b⟩, hab, he⟩
      obtain ⟨-, -, -, -, -, hKa⟩ := sel_necessary hN hsf h12 hM hab
      simp only [Prod.mk.injEq] at he
      rw [← he.1, ← he.2]
      exact ⟨hker _ hKa, zmod2_cases _⟩
    · rintro ⟨hu, hσ⟩
      have hget : ∀ c : ℕ, c ∣ ℓ → ind ℓ (c : ℤ) = u → Kmat ℓ *ᵥ u = 0 →
          (u, σ) ∈ (fun ab : ℤ × ℤ => (ind ℓ ab.1, sg ab.2)) '' SelM ℓ := by
        intro c hc hcu hK
        rw [← hcu] at hK
        rcases hσ with rfl | rfl
        · exact ⟨_, (hcand c hc hK false).1, (hcand c hc hK false).2.trans (by rw [hcu]; rfl)⟩
        · exact ⟨_, (hcand c hc hK true).1, (hcand c hc hK true).2.trans (by rw [hcu]; rfl)⟩
      rcases hu with rfl | rfl | rfl | rfl
      · exact hget 1 (one_dvd _) hind1 (mulVec_zero _)
      · exact hget ℓ dvd_rfl ind_ell kmat_mulVec_one
      · exact hget β hβℓ hindβ hKb
      · exact hget ℓ' hℓ'd hindℓ' hK1
  have hinj := sel_injOn hN hsf h12 hM
  refine ⟨?_, ?_⟩
  · rw [← hinj.ncard_image, himage, Set.ncard_coe_finset, Finset.card_product]
    obtain ⟨⟨h01, h0b, h01b⟩, ⟨h1b, h11b⟩, hb1b⟩ := vec4_ne hb0 hb1
    rw [Finset.card_insert_of_notMem (by simp [h01, h0b, h01b]),
      Finset.card_insert_of_notMem (by simp [h1b, h11b]),
      Finset.card_insert_of_notMem (by simp [hb1b])]
    rfl
  · have := (hcand β hβℓ (by rw [hindβ]; exact hKb) false).1
    simpa using this

end ZInQ.Manuscript.PoleRC
