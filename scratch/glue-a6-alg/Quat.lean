/-
glue-a6-alg: proof of the pure-algebra glue `QuatUnipotentTrivial` of rv-a6-route
(docs/research/rv-a6-route.md §3), in module form over `V = Fin 4 → ZMod (3^{2k})`.
§1 is a verbatim copy of scratch/rv-a6-route/QuatVal.lean (namespace renamed).
-/
import Mathlib

namespace GlueA6Alg

lemma three_prime : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.mpr Nat.prime_three

lemma dvd_of_dvd_two_mul {a y : ℤ} (ha : ¬ (3 : ℤ) ∣ a) (h : (3 : ℤ) ∣ 2 * a * y) : (3 : ℤ) ∣ y := by
  rcases three_prime.dvd_or_dvd h with h' | h'
  · rcases three_prime.dvd_or_dvd h' with h'' | h''
    · norm_num at h''
    · exact absurd h'' ha
  · exact h'

lemma nine_dvd_of_dvd_two_mul {a y : ℤ} (ha : ¬ (3 : ℤ) ∣ a) (h : (9 : ℤ) ∣ 2 * a * y) :
    (9 : ℤ) ∣ y := by
  have h3 : (3 : ℤ) ∣ y := dvd_of_dvd_two_mul ha (dvd_trans ⟨3, by norm_num⟩ h)
  obtain ⟨y', rfl⟩ := h3
  have h' : (3 : ℤ) ∣ 2 * a * y' := by
    have : (3 : ℤ) * 3 ∣ 3 * (2 * a * y') := by
      have e : (3 : ℤ) * (2 * a * y') = 2 * a * (3 * y') := by ring
      rw [e]; simpa using h
    exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).mp this
  have := dvd_of_dvd_two_mul ha h'
  obtain ⟨z, rfl⟩ := this
  exact ⟨z, by ring⟩

lemma zmod3_aniso : ∀ x y : ZMod 3, 2 * y ^ 2 - x ^ 2 = 0 → x = 0 ∧ y = 0 := by decide

/-- Base case: `9 ∣` every coordinate of `x²` implies `3 ∣` every coordinate of `x`. -/
lemma quat_base (a b c d : ℤ) (h1 : (9 : ℤ) ∣ a ^ 2 + 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2)
    (h2 : (9 : ℤ) ∣ 2 * a * b) (h3 : (9 : ℤ) ∣ 2 * a * c) (h4 : (9 : ℤ) ∣ 2 * a * d) :
    (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b ∧ (3 : ℤ) ∣ c ∧ (3 : ℤ) ∣ d := by
  have ha : (3 : ℤ) ∣ a := by
    by_contra ha
    have hb := nine_dvd_of_dvd_two_mul ha h2
    have hc := nine_dvd_of_dvd_two_mul ha h3
    have hd := nine_dvd_of_dvd_two_mul ha h4
    have e : a ^ 2 = (a ^ 2 + 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2) - (2 * b) * b + (3 * c) * c
        - (6 * d) * d := by ring
    have h9 : (9 : ℤ) ∣ a ^ 2 := by
      rw [e]
      exact dvd_sub (dvd_add (dvd_sub h1 (Dvd.dvd.mul_left hb _)) (Dvd.dvd.mul_left hc _))
        (Dvd.dvd.mul_left hd _)
    exact ha (three_prime.dvd_of_dvd_pow (dvd_trans ⟨3, by norm_num⟩ h9))
  obtain ⟨a', rfl⟩ := ha
  have hb : (3 : ℤ) ∣ b := by
    have e : 2 * b ^ 2 = ((3 * a') ^ 2 + 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2) - 3 * (3 * a' ^ 2)
        + 3 * (c ^ 2) - 3 * (2 * d ^ 2) := by ring
    have h3b : (3 : ℤ) ∣ 2 * b ^ 2 := by
      rw [e]
      exact dvd_sub (dvd_add (dvd_sub (dvd_trans ⟨3, by norm_num⟩ h1) (dvd_mul_right _ _))
        (dvd_mul_right _ _)) (dvd_mul_right _ _)
    rcases three_prime.dvd_or_dvd h3b with h | h
    · norm_num at h
    · exact three_prime.dvd_of_dvd_pow h
  obtain ⟨b', rfl⟩ := hb
  have hcd : (3 : ℤ) ∣ 2 * d ^ 2 - c ^ 2 := by
    have e : (3 : ℤ) * (2 * d ^ 2 - c ^ 2) = ((3 * a') ^ 2 + 2 * (3 * b') ^ 2 - 3 * c ^ 2
        + 6 * d ^ 2) - 9 * (a' ^ 2 + 2 * b' ^ 2) := by ring
    have : (3 : ℤ) * 3 ∣ 3 * (2 * d ^ 2 - c ^ 2) := by
      rw [e]; exact dvd_sub (by simpa using h1) (dvd_mul_right _ _)
    exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).mp this
  have hz : (((2 * d ^ 2 - c ^ 2 : ℤ)) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast hcd)
  push_cast at hz
  obtain ⟨hc0, hd0⟩ := zmod3_aniso _ _ hz
  refine ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ?_, ?_⟩
  · exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd c 3).mp hc0
  · exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd d 3).mp hd0

/-- **Valuation step (proved).** If `3^{2k}` divides every coordinate of
`(a + bi + cj + d·ij)²` in `Λ = ℤ⟨i,j⟩`, then `3^k` divides `a, b, c, d`. -/
theorem quat_sq_dvd (k : ℕ) : ∀ a b c d : ℤ,
    (3 : ℤ) ^ (2 * k) ∣ a ^ 2 + 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2 →
    (3 : ℤ) ^ (2 * k) ∣ 2 * a * b → (3 : ℤ) ^ (2 * k) ∣ 2 * a * c →
    (3 : ℤ) ^ (2 * k) ∣ 2 * a * d →
    (3 : ℤ) ^ k ∣ a ∧ (3 : ℤ) ^ k ∣ b ∧ (3 : ℤ) ^ k ∣ c ∧ (3 : ℤ) ^ k ∣ d := by
  induction k with
  | zero => intros; simp
  | succ k ih =>
    intro a b c d h1 h2 h3 h4
    have e9 : (3 : ℤ) ^ (2 * (k + 1)) = 9 * 3 ^ (2 * k) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; norm_num; ring
    rw [e9] at h1 h2 h3 h4
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩, ⟨d', rfl⟩⟩ :=
      quat_base a b c d (dvd_of_mul_right_dvd h1) (dvd_of_mul_right_dvd h2)
        (dvd_of_mul_right_dvd h3) (dvd_of_mul_right_dvd h4)
    have cancel : ∀ z : ℤ, 9 * 3 ^ (2 * k) ∣ 9 * z → 3 ^ (2 * k) ∣ z := fun z hz =>
      (mul_dvd_mul_iff_left (by norm_num : (9 : ℤ) ≠ 0)).mp hz
    have := ih a' b' c' d'
      (cancel _ (by convert h1 using 1; ring)) (cancel _ (by convert h2 using 1; ring))
      (cancel _ (by convert h3 using 1; ring)) (cancel _ (by convert h4 using 1; ring))
    obtain ⟨⟨a'', rfl⟩, ⟨b'', rfl⟩, ⟨c'', rfl⟩, ⟨d'', rfl⟩⟩ := this
    exact ⟨⟨a'', by ring⟩, ⟨b'', by ring⟩, ⟨c'', by ring⟩, ⟨d'', by ring⟩⟩


/-! ## 2. Independence over `𝔽₃` -/

lemma f3_aniso : ∀ a b : ZMod 3, a ^ 2 - 2 * b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide

/-- Over `𝔽₃`: if `I² = 2`, `J² = 0`, `JI = -IJ` and `Jx ≠ 0`, then `x, Ix, Jx, IJx` are
linearly independent (because `a² - 2b²` is anisotropic mod 3). -/
lemma f3_indep {M : Type*} [AddCommGroup M] [Module (ZMod 3) M] (I J : M →ₗ[ZMod 3] M)
    (hI : ∀ y, I (I y) = (2 : ZMod 3) • y) (hJ : ∀ y, J (J y) = 0)
    (hIJ : ∀ y, J (I y) = -I (J y)) (x : M) (hx : J x ≠ 0) :
    LinearIndependent (ZMod 3) ![x, I x, J x, I (J x)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hg
  have h1 : g 0 • J x - g 1 • I (J x) = 0 := by
    have := congrArg J hg
    simp only [map_add, map_smul, hJ, hIJ, map_zero, smul_neg, smul_zero,
      add_zero] at this
    linear_combination (norm := module) this
  have h2 : g 0 • I (J x) - g 1 • (2 : ZMod 3) • J x = 0 := by
    have := congrArg I h1
    simp only [map_sub, map_smul, hI, map_zero] at this
    exact this
  have k1 : (g 0 ^ 2 - 2 * g 1 ^ 2) • J x = 0 := by
    linear_combination (norm := module) g 0 • h1 + g 1 • h2
  obtain ⟨g0, g1⟩ := f3_aniso _ _ ((smul_eq_zero.mp k1).resolve_right hx)
  rw [g0, g1, zero_smul, zero_smul, zero_add, zero_add] at hg
  have h3 : g 2 • I (J x) + g 3 • (2 : ZMod 3) • J x = 0 := by
    have := congrArg I hg
    simp only [map_add, map_smul, hI, map_zero] at this
    exact this
  have k2 : (g 2 ^ 2 - 2 * g 3 ^ 2) • J x = 0 := by
    linear_combination (norm := module) g 2 • hg - g 3 • h3
  obtain ⟨g2, g3⟩ := f3_aniso _ _ ((smul_eq_zero.mp k2).resolve_right hx)
  intro i
  fin_cases i <;> assumption

/-! ## 3. The core: `T ≅ (ℤ/3^{2k})⁴` is cyclic over `Λ`, and `S - 1` is divisible by `3^k` -/

section Core

variable (k : ℕ)

abbrev Q : ℕ := 3 ^ (2 * k)

instance : NeZero (Q k) := ⟨by positivity⟩

abbrev R := ZMod (Q k)

abbrev V := Fin 4 → R k

variable {k}

/-- `φ y a = a₀ y + a₁ I y + a₂ J y + a₃ I J y`: the orbit map `Λ/q → T` at `y`. -/
def φ (I J : V k →ₗ[R k] V k) (y : V k) (a : Fin 4 → R k) : V k :=
  a 0 • y + a 1 • I y + a 2 • J y + a 3 • I (J y)

lemma φ_add_smul (I J : V k →ₗ[R k] V k) (y : V k) (a b : Fin 4 → R k) (c : R k) :
    φ I J y (a + c • b) = φ I J y a + c • φ I J y b := by
  simp only [φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; module

lemma φ_smul (I J : V k →ₗ[R k] V k) (y : V k) (a : Fin 4 → R k) (c : R k) :
    φ I J y (c • a) = c • φ I J y a := by
  simp only [φ, Pi.smul_apply, smul_eq_mul]; module

lemma φ_sub (I J : V k →ₗ[R k] V k) (y : V k) (a b : Fin 4 → R k) :
    φ I J y (a - b) = φ I J y a - φ I J y b := by
  simp only [φ, Pi.sub_apply]; module

lemma φ_zero (I J : V k →ₗ[R k] V k) (y : V k) : φ I J y 0 = 0 := by
  simp [φ]

lemma φ_smul_left (I J : V k →ₗ[R k] V k) (y : V k) (a : Fin 4 → R k) (c : R k) :
    φ I J (c • y) a = φ I J y (c • a) := by
  simp only [φ, map_smul, Pi.smul_apply, smul_eq_mul]; module

lemma φ_sub_left (I J : V k →ₗ[R k] V k) (y z : V k) (a : Fin 4 → R k) :
    φ I J (y - z) a = φ I J y a - φ I J z a := by
  simp only [φ, map_sub]; module

lemma Q_natCast : ((Q k : ℕ) : R k) = 0 := ZMod.natCast_self _

lemma three_pow_eq_zero : (3 : R k) ^ (2 * k) = 0 := by
  have := Q_natCast (k := k); push_cast [Q] at this; exact this

lemma three_dvd_Q (hk : 1 ≤ k) : 3 ∣ Q k := dvd_pow_self 3 (by omega)

lemma nine_dvd_Q (hk : 1 ≤ k) : 9 ∣ Q k := by
  have : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [this]; exact pow_dvd_pow 3 (by omega)

/-- If `z ≡ 0 (mod 3)` then `z = 3y`. -/
lemma eq_three_mul_of_cast_eq_zero (hk : 1 ≤ k) (z : R k)
    (hz : ZMod.castHom (three_dvd_Q hk) (ZMod 3) z = 0) : ∃ y : R k, z = 3 * y := by
  have h0 : ((z.val : ℕ) : ZMod 3) = 0 := by
    rw [← map_natCast (ZMod.castHom (three_dvd_Q hk) (ZMod 3)), ZMod.natCast_zmod_val]; exact hz
  obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff _ _).mp h0
  refine ⟨(m : R k), ?_⟩
  rw [← ZMod.natCast_zmod_val z, hm]; push_cast; ring

/-- Coordinatewise reduction mod 3. -/
def red (hk : 1 ≤ k) (v : V k) : Fin 4 → ZMod 3 := fun i => ZMod.castHom (three_dvd_Q hk) (ZMod 3) (v i)

lemma red_add (hk : 1 ≤ k) (v w : V k) : red hk (v + w) = red hk v + red hk w := by
  funext i; simp only [red, Pi.add_apply, map_add]

lemma red_sub (hk : 1 ≤ k) (v w : V k) : red hk (v - w) = red hk v - red hk w := by
  funext i; simp only [red, Pi.sub_apply, map_sub]

lemma red_neg (hk : 1 ≤ k) (v : V k) : red hk (-v) = -red hk v := by
  funext i; simp only [red, Pi.neg_apply, map_neg]

lemma red_smul (hk : 1 ≤ k) (c : R k) (v : V k) :
    red hk (c • v) = ZMod.castHom (three_dvd_Q hk) (ZMod 3) c • red hk v := by
  funext i; simp only [red, Pi.smul_apply, smul_eq_mul, map_mul]

lemma eq_three_smul_of_red_eq_zero (hk : 1 ≤ k) (v : V k) (hv : red hk v = 0) :
    ∃ u : V k, v = (3 : R k) • u := by
  have h := fun i => eq_three_mul_of_cast_eq_zero hk (v i) (congrFun hv i)
  choose u hu using h
  exact ⟨u, funext fun i => by simpa using hu i⟩

/-- Lift of a vector mod 3. -/
def lift3 (y : Fin 4 → ZMod 3) : V k := fun i => ((y i).val : R k)

lemma red_lift3 (hk : 1 ≤ k) (y : Fin 4 → ZMod 3) : red hk (lift3 y) = y := by
  funext i; simp [red, lift3]

/-- The reduction of a linear map, as a matrix over `𝔽₃`. -/
noncomputable def redMap (hk : 1 ≤ k) (f : V k →ₗ[R k] V k) :
    (Fin 4 → ZMod 3) →ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.mulVecLin ((LinearMap.toMatrix' f).map (ZMod.castHom (three_dvd_Q hk) (ZMod 3)))

lemma red_map (hk : 1 ≤ k) (f : V k →ₗ[R k] V k) (v : V k) :
    red hk (f v) = redMap hk f (red hk v) := by
  funext i
  simp only [red, redMap, Matrix.mulVecLin_apply]
  rw [← LinearMap.toMatrix'_mulVec f v, RingHom.map_mulVec]
  rfl

end Core

end GlueA6Alg
