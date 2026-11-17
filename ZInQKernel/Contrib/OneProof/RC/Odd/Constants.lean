import Mathlib

/-!
# Lane RC12-odd: the constant `c₀ = |GL₄(𝔽₃)|` of the odd theta sum (App F, tex 8598–8621, 9372–9399)

Manuscript (11/5), Appendix F, Proposition `ex:app-theta-form`, the paragraph after (O.4):
"Set `c₀ = |GL₄(𝔽₃)| = 24 261 120`, so `v₂(c₀) = 9` … Left multiplication embeds each `R_z^×` into
`GL₄(ℤ)`; reduction modulo three is injective on finite subgroups … Thus `|R_z^×| ∣ c₀`"
(tex 8598–8611), and the precision paragraph of `ex:app-theta-comparison` ("`-1 ∈ R_z^×` implies
`2 ∣ |R_z^×|` … hence `c₀/2` is an integer … each orbit contributes `(c₀/|R_z^×|)(|R_z^×|/2) P_M(z)
= (c₀/2) P_M(z)`", tex 9378–9390; "`c_θ = 9 + ω(N)`, the valuation of `c₀ 2^{ω(N)}`", 9391–9392).

Everything here is PROVED.
-/

namespace ZInQ.Manuscript.RC.Odd

open Matrix

/-- `c₀ = |GL₄(𝔽₃)| = 24 261 120` (tex 8414, 8598). -/
def c0 : ℕ := 24261120

/-- **PROVED.** `|GL₄(𝔽₃)| = c₀` (tex 8598). -/
theorem card_GL4_ZMod3 : Nat.card (GL (Fin 4) (ZMod 3)) = c0 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_four, ZMod.card, c0]

theorem c0_eq : c0 = 2 ^ 9 * 47385 := by norm_num [c0]

/-- **PROVED.** `v₂(c₀) = 9` (tex 8599). -/
theorem padicValNat_two_c0 : padicValNat 2 c0 = 9 := by
  rw [c0_eq, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
  have : padicValNat 2 47385 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  omega

/-- **PROVED.** `c_θ = 9 + ω(N)` is the 2-adic valuation of `c₀ 2^{ω(N)}` (tex 9391–9392). -/
theorem padicValNat_c0_mul_two_pow (w : ℕ) : padicValNat 2 (c0 * 2 ^ w) = 9 + w := by
  rw [padicValNat.mul (by norm_num [c0]) (by positivity), padicValNat.prime_pow,
    padicValNat_two_c0]

/-! ### Reduction modulo three is injective on finite subgroups of `GL_n(ℤ)` -/

/-- The binomial step (tex 8607–8610): if `(1 + 3^a A)^p = 1` with `a ≥ 1` and `p` prime, then
every entry of `A` is divisible by `3`. -/
theorem three_dvd_of_pow_eq_one {n : ℕ} {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (A : Matrix (Fin n) (Fin n) ℤ) (h : (1 + (3 : ℤ) ^ a • A) ^ p = 1) (i j : Fin n) :
    (3 : ℤ) ∣ A i j := by
  set X : Matrix (Fin n) (Fin n) ℤ := (3 : ℤ) ^ a • A with hX
  by_cases h3 : p = 3
  · subst h3
    have hexp : (1 + X) ^ 3 = 1 + (3 : ℤ) • X + (3 : ℤ) • X ^ 2 + X ^ 3 := by
      simp only [pow_succ, pow_zero, one_mul, mul_add, add_mul, mul_one, one_mul]
      module
    rw [hexp] at h
    have h0 : (3 : ℤ) • X + (3 : ℤ) • X ^ 2 + X ^ 3 = 0 := by
      have := congrArg (· - 1) h
      simp only [sub_self] at this
      rw [← this]; abel
    have he := congrFun (congrFun h0 i) j
    simp only [hX, smul_pow, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply] at he
    -- 3^(a+1) A + 3^(2a+1) A² + 3^(3a) A³ = 0
    have hd : (3 : ℤ) ^ (a + 2) ∣ 3 ^ (a + 1) * A i j := by
      have e1 : (3 : ℤ) ^ (a + 1) * A i j =
          -(3 * ((3 ^ a) ^ 2 * (A ^ 2) i j) + (3 ^ a) ^ 3 * (A ^ 3) i j) := by
        rw [pow_succ]; linarith [he]
      rw [e1]
      apply dvd_neg.mpr
      apply dvd_add
      · have : (3 : ℤ) * ((3 ^ a) ^ 2 * (A ^ 2) i j) = 3 ^ (a + 2) * (3 ^ (a - 1) * (A ^ 2) i j)
          := by
          rw [← pow_mul, ← mul_assoc, ← mul_assoc, ← pow_succ', ← pow_add]
          congr 2; omega
        rw [this]; exact dvd_mul_right _ _
      · have : ((3 : ℤ) ^ a) ^ 3 * (A ^ 3) i j = 3 ^ (a + 2) * (3 ^ (2 * a - 2) * (A ^ 3) i j)
          := by
          rw [← pow_mul, ← mul_assoc, ← pow_add]
          congr 2; omega
        rw [this]; exact dvd_mul_right _ _
    rw [show a + 2 = (a + 1) + 1 by ring, pow_succ] at hd
    exact (mul_dvd_mul_iff_left (by positivity)).mp hd
  · -- `p ≠ 3`: work modulo `3^(a+1)`
    have hc : Commute X 1 := Commute.one_right X
    have hsum := hc.add_pow p
    rw [add_comm X 1, h] at hsum
    have he := congrFun (congrFun hsum i) j
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at he
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, zero_add,
      pow_one, Nat.choose_one_right, Matrix.add_apply] at he
    have hnat : ∀ (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ), (M * (k : Matrix (Fin n) (Fin n) ℤ)) i j
        = M i j * k := by
      intro M k
      rw [← Matrix.diagonal_natCast', Matrix.mul_diagonal]; rfl
    simp only [Matrix.sum_apply, hnat, Matrix.one_apply] at he
    have hrest : (3 : ℤ) ^ (a + 1) ∣
        ∑ x ∈ Finset.range q, (X ^ (x + 1 + 1)) i j * ((q + 1).choose (x + 1 + 1) : ℕ) := by
      apply Finset.dvd_sum
      intro x _
      apply Dvd.dvd.mul_right
      rw [hX, smul_pow, Matrix.smul_apply, smul_eq_mul, ← pow_mul]
      apply Dvd.dvd.mul_right
      exact pow_dvd_pow 3 (by nlinarith)
    have h1 : (3 : ℤ) ^ (a + 1) ∣ X i j * ((q + 1 : ℕ) : ℤ) := by
      have : X i j * ((q + 1 : ℕ) : ℤ) =
          (1 : Matrix (Fin n) (Fin n) ℤ) i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j -
          ∑ x ∈ Finset.range q, (X ^ (x + 1 + 1)) i j * ((q + 1).choose (x + 1 + 1) : ℕ) := by
        simp only [Matrix.one_apply] at he ⊢
        push_cast at he ⊢
        linarith
      rw [this, sub_self, zero_sub]
      exact dvd_neg.mpr hrest
    rw [hX, Matrix.smul_apply, smul_eq_mul, pow_succ, mul_assoc] at h1
    have h2 : (3 : ℤ) ∣ A i j * ((q + 1 : ℕ) : ℤ) :=
      (mul_dvd_mul_iff_left (by positivity)).mp h1
    rcases (Int.prime_three.dvd_or_dvd h2) with h4 | h4
    · exact h4
    · exfalso
      have : (3 : ℕ) ∣ q + 1 := by exact_mod_cast h4
      exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp this).symm

/-- If `h^p = 1` (`p` prime) and `h ≡ 1 (mod 3)` entrywise, then `h = 1`. -/
theorem eq_one_of_pow_prime_eq_one {n : ℕ} {p : ℕ} (hp : p.Prime)
    (h : Matrix (Fin n) (Fin n) ℤ) (hpow : h ^ p = 1) (h3 : ∀ i j, (3 : ℤ) ∣ (h - 1) i j) :
    h = 1 := by
  have key : ∀ a : ℕ, 1 ≤ a → ∀ i j, (3 : ℤ) ^ a ∣ (h - 1) i j := by
    intro a ha
    induction a, ha using Nat.le_induction with
    | base => simpa using h3
    | succ a ha ih =>
      choose A hA using ih
      let A' : Matrix (Fin n) (Fin n) ℤ := fun i j => A i j
      have hh : h = 1 + (3 : ℤ) ^ a • A' := by
        ext i j
        have := hA i j
        rw [Matrix.sub_apply] at this
        change h i j = (1 : Matrix (Fin n) (Fin n) ℤ) i j + 3 ^ a * A i j
        linarith
      have hd := three_dvd_of_pow_eq_one hp ha A' (hh ▸ hpow)
      intro i j
      rw [hA i j, pow_succ]
      exact mul_dvd_mul_left _ (hd i j)
  ext i j
  have hz : (h - 1) i j = 0 := by
    by_contra hne
    have hlt : ((h - 1) i j).natAbs < 3 ^ ((h - 1) i j).natAbs :=
      Nat.lt_pow_self (by norm_num)
    have hd := key ((h - 1) i j).natAbs (Int.natAbs_pos.mpr hne) i j
    have := Int.natAbs_dvd_natAbs.mpr hd
    simp only [Int.natAbs_pow] at this
    exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hne) this) (by simpa using hlt)
  simpa [Matrix.sub_apply, sub_eq_zero] using hz

/-- **PROVED (Minkowski; tex 8605–8611).** Reduction modulo three is injective on every finite
group of integral matrices: if `f : H →* GL_n(ℤ)` is injective and `H` is finite, then so is its
composite with reduction modulo three. -/
theorem reduction_mod_three_injective {n : ℕ} {H : Type*} [Group H] [Finite H]
    (f : H →* GL (Fin n) ℤ) (hf : Function.Injective f) :
    Function.Injective ((Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 3))).comp f) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hne
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  have hk : 1 < orderOf g := by
    have h1 := orderOf_pos_iff.mpr hfin
    have h2 : orderOf g ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    omega
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (by omega : orderOf g ≠ 1)
  set g' := g ^ (orderOf g / p)
  have hord : orderOf g' = p := orderOf_pow_orderOf_div (by omega) hpk
  have hg'1 : (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 3))).comp f g' = 1 := by
    simp only [g', map_pow, hg, one_pow]
  have hmat : ((f g' : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) = 1 := by
    apply eq_one_of_pow_prime_eq_one hp
    · rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hord, pow_orderOf_eq_one, map_one]; rfl
    · intro i j
      have := congrArg (fun u : GL (Fin n) (ZMod 3) => (u : Matrix (Fin n) (Fin n) (ZMod 3)) i j)
        hg'1
      simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, Units.val_one,
        RingHom.mapMatrix_apply] at this
      have key : ((((f g' : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) i j -
          (1 : Matrix (Fin n) (Fin n) ℤ) i j : ℤ) : ZMod 3) = 0 := by
        rw [Int.cast_sub]
        simp only [Matrix.map_apply, Int.coe_castRingHom] at this
        rw [this]
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp key
      simpa [Matrix.sub_apply] using this
  have : f g' = 1 := Units.ext (by simpa using hmat)
  rw [← map_one f] at this
  have h1 : g' = 1 := hf this
  rw [h1, orderOf_one] at hord
  exact hp.one_lt.ne hord

/-- **PROVED (tex 8611).** Every finite group of integral `4 × 4` matrices has order dividing
`c₀ = |GL₄(𝔽₃)|`. -/
theorem card_dvd_c0_of_injective {H : Type*} [Group H] [Finite H] (f : H →* GL (Fin 4) ℤ)
    (hf : Function.Injective f) : Nat.card H ∣ c0 :=
  card_GL4_ZMod3 ▸ Subgroup.card_dvd_of_injective _ (reduction_mod_three_injective f hf)

/-- **PROVED (tex 8611).** Every finite subgroup of `GL₄(ℤ)` has order dividing `c₀`. -/
theorem card_dvd_c0_of_finite_subgroup (G : Subgroup (GL (Fin 4) ℤ)) [Finite G] :
    Nat.card G ∣ c0 :=
  card_dvd_c0_of_injective G.subtype Subtype.val_injective

/-- **PROVED (tex 8605–8611).** For an order `R_z` with a `ℤ`-basis of rank four, left
multiplication embeds `R_z^×` into `GL₄(ℤ)`, so every finite subgroup of `R_z^×` has order dividing
`c₀`. (That `R_z = B ∩ z R̂ z⁻¹` is free of rank four over `ℤ`, and that `R_z^×` is finite for the
definite algebra `B`, is GLUE.) -/
theorem card_dvd_c0_of_basis {R : Type*} [Ring R] (b : Module.Basis (Fin 4) ℤ R)
    (G : Subgroup Rˣ) [Finite G] : Nat.card G ∣ c0 := by
  let φ : Rˣ →* GL (Fin 4) ℤ := Units.map (Algebra.leftMulMatrix b).toMonoidHom
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Units.ext
    exact Algebra.leftMulMatrix_injective b (congrArg Units.val hxy)
  exact card_dvd_c0_of_injective (φ.comp G.subtype) (hφ.comp Subtype.val_injective)

/-- **PROVED (tex 9379–9390).** If `w = |R_z^×|` is even and divides `c₀`, then each embedding
orbit (of size `w/2`, stabilizer `{±1}`) weighted by `c₀/w` contributes exactly `c₀/2`; `c₀/2` is an
integer, so no congruence modulo `2^M` is divided by two. -/
theorem orbit_weight_eq' (N w : ℕ) (hw2 : 2 ∣ w) (hw : w ∣ N) : (N / w) * (w / 2) = N / 2 := by
  obtain ⟨k, rfl⟩ := hw
  obtain ⟨j, rfl⟩ := hw2
  rcases Nat.eq_zero_or_pos j with h0 | hj
  · subst h0; simp
  · rw [Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)]
    rw [show 2 * j * k = 2 * (j * k) by ring, Nat.mul_div_cancel_left _ (by omega)]
    ring

theorem orbit_weight_eq (w : ℕ) (hw2 : 2 ∣ w) (hw : w ∣ c0) : (c0 / w) * (w / 2) = c0 / 2 :=
  orbit_weight_eq' c0 w hw2 hw

end ZInQ.Manuscript.RC.Odd
