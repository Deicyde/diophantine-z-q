/-
glue-a6-alg: proof of the pure-algebra glue `QuatUnipotentTrivial` of rv-a6-route
(docs/research/rv-a6-route.md §3), in module form over `V = Fin 4 → ZMod (3^{2k})`.
§1 is a verbatim copy of scratch/rv-a6-route/QuatVal.lean (namespace renamed).
-/
import Mathlib

universe u

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

/-- **Core (proved).** On `V = (ℤ/3^{2k})⁴` (`k ≥ 1`), let `I, J, S` be endomorphisms with
`I² = 2`, `J² = -3`, `JI = -IJ`, `S` commuting with `I, J` and `(S - 1)² = 0`. Then `S` is the
identity on the `3^k`-torsion. (rv-a6-route §3 steps 1-5: `V` is cyclic over `Λ` with generator
`x` (any `x` with `Jx ≢ 0 mod 3`), `S x - x = c·x` with `c² = 0` in `Λ/3^{2k}`, so `c ∈ 3^kΛ`.) -/
theorem core (hk : 1 ≤ k) (I J S : V k →ₗ[R k] V k)
    (hI : ∀ v, I (I v) = (2 : R k) • v) (hJ : ∀ v, J (J v) = (-3 : R k) • v)
    (hIJ : ∀ v, J (I v) = -I (J v))
    (hSI : ∀ v, S (I v) = I (S v)) (hSJ : ∀ v, S (J v) = J (S v))
    (hS : ∀ v, S (S v) - (2 : R k) • S v + v = 0) :
    ∀ v, (3 : R k) ^ k • v = 0 → S v = v := by
  -- the reduced relations over `𝔽₃`
  have hIb : ∀ y, redMap hk I (redMap hk I y) = (2 : ZMod 3) • y := by
    intro y
    rw [← red_lift3 hk y, ← red_map, ← red_map, hI, red_smul, map_ofNat]
  have hJb : ∀ y, redMap hk J (redMap hk J y) = 0 := by
    intro y
    rw [← red_lift3 hk y, ← red_map, ← red_map, hJ, red_smul]
    have : ZMod.castHom (three_dvd_Q hk) (ZMod 3) (-3 : R k) = 0 := by
      rw [map_neg, map_ofNat]; decide
    rw [this, zero_smul]
  have hIJb : ∀ y, redMap hk J (redMap hk I y) = -redMap hk I (redMap hk J y) := by
    intro y
    rw [← red_lift3 hk y, ← red_map, ← red_map, ← red_map, ← red_map, hIJ, red_neg]
  -- step 1: some `x` has `J x ≢ 0 (mod 3)`
  have hex : ∃ x : V k, red hk (J x) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨u, hu⟩ := eq_three_smul_of_red_eq_zero hk _ (h (Pi.single (0 : Fin 4) (1 : R k)))
    obtain ⟨u', hu'⟩ := eq_three_smul_of_red_eq_zero hk _ (h u)
    have e := hJ (Pi.single (0 : Fin 4) (1 : R k))
    rw [hu, map_smul, hu', smul_smul] at e
    have e0 := congrFun e 0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] at e0
    have e9 := congrArg (ZMod.castHom (nine_dvd_Q hk) (ZMod 9)) e0
    simp only [map_mul, map_neg, map_ofNat] at e9
    have h9 : ∀ z : ZMod 9, 3 * 3 * z ≠ -3 := by decide
    exact h9 _ e9
  obtain ⟨x, hx⟩ := hex
  have hx' : redMap hk J (red hk x) ≠ 0 := by rwa [← red_map]
  -- step 2: `x, Ix, Jx, IJx` span `V/3V`
  have hli := f3_indep (redMap hk I) (redMap hk J) hIb hJb hIJb (red hk x) hx'
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp)
  have mod3 : ∀ u : V k, ∃ a : Fin 4 → R k, ∃ u' : V k, u = φ I J x a + (3 : R k) • u' := by
    intro u
    have hu : red hk u ∈ Submodule.span (ZMod 3) (Set.range ![red hk x, redMap hk I (red hk x),
        redMap hk J (red hk x), redMap hk I (redMap hk J (red hk x))]) := by
      rw [hspan]; trivial
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hu
    refine ⟨fun i => ((g i).val : R k), ?_⟩
    have hred : red hk (u - φ I J x (fun i => ((g i).val : R k))) = 0 := by
      rw [red_sub, ← hg, sub_eq_zero]
      simp only [φ, red_add, red_smul, red_map, Fin.sum_univ_four, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, map_natCast, ZMod.natCast_zmod_val]
    obtain ⟨u', hu'⟩ := eq_three_smul_of_red_eq_zero hk _ hred
    exact ⟨u', by rw [← hu']; abel⟩
  -- step 2': Nakayama, `V = Λ x`
  have nak : ∀ n : ℕ, ∀ u : V k, ∃ a : Fin 4 → R k, ∃ u' : V k,
      u = φ I J x a + (3 : R k) ^ n • u' := by
    intro n
    induction n with
    | zero => intro u; exact ⟨0, u, by rw [φ_zero, pow_zero, one_smul, zero_add]⟩
    | succ n ih =>
      intro u
      obtain ⟨a, u', h⟩ := ih u
      obtain ⟨b, u'', h'⟩ := mod3 u'
      refine ⟨a + (3 : R k) ^ n • b, u'', ?_⟩
      rw [φ_add_smul, h, h', pow_succ]; module
  have hsurj : Function.Surjective (φ I J x) := by
    intro u
    obtain ⟨a, u', h⟩ := nak (2 * k) u
    exact ⟨a, by rw [h, three_pow_eq_zero, zero_smul, add_zero]⟩
  have hinj : Function.Injective (φ I J x) := Finite.injective_iff_surjective.mpr hsurj
  have hinj0 : ∀ a, φ I J x a = 0 → a = 0 := fun a ha => hinj (by rw [ha, φ_zero])
  -- step 3: `S x - x = c x` with `c² = 0`
  have hSφ : ∀ y a, S (φ I J y a) = φ I J (S y) a := by
    intro y a; simp only [φ, map_add, map_smul, hSI, hSJ]
  obtain ⟨a, ha⟩ := hsurj (S x - x)
  have hsq : φ I J (φ I J x a) a = φ I J x ![a 0 ^ 2 + 2 * a 1 ^ 2 - 3 * a 2 ^ 2 + 6 * a 3 ^ 2,
      2 * a 0 * a 1, 2 * a 0 * a 2, 2 * a 0 * a 3] := by
    simp only [φ, map_add, map_smul, map_neg, hI, hJ, hIJ, smul_neg, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]
    module
  have hNN : φ I J (φ I J x a) a = 0 := by
    rw [ha, φ_sub_left, ← hSφ, ha, map_sub]
    linear_combination (norm := module) hS x
  have hc := hinj0 _ (hsq ▸ hNN)
  have c0 := congrFun hc 0
  have c1 := congrFun hc 1
  have c2 := congrFun hc 2
  have c3 := congrFun hc 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at c0 c1 c2 c3
  -- step 4: `c ∈ 3^k Λ` (`quat_sq_dvd`)
  have hdvd : ∀ z : ℤ, (z : R k) = 0 → (3 : ℤ) ^ (2 * k) ∣ z := by
    intro z hz
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    simpa [Q] using this
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩, ⟨C, hC⟩, ⟨D, hD⟩⟩ := quat_sq_dvd k ((a 0).val : ℤ) ((a 1).val : ℤ)
    ((a 2).val : ℤ) ((a 3).val : ℤ)
    (hdvd _ (by push_cast [ZMod.natCast_zmod_val]; exact c0))
    (hdvd _ (by push_cast [ZMod.natCast_zmod_val]; exact c1))
    (hdvd _ (by push_cast [ZMod.natCast_zmod_val]; exact c2))
    (hdvd _ (by push_cast [ZMod.natCast_zmod_val]; exact c3))
  have lift : ∀ (i : Fin 4) (E : ℤ), ((a i).val : ℤ) = 3 ^ k * E → a i = (3 : R k) ^ k * (E : R k) := by
    intro i E h
    have := congrArg (fun z : ℤ => (z : R k)) h
    push_cast [ZMod.natCast_zmod_val] at this
    exact this
  have ha' : a = (3 : R k) ^ k • ![(A : R k), (B : R k), (C : R k), (D : R k)] := by
    funext i
    fin_cases i
    · simpa using lift 0 A hA
    · simpa using lift 1 B hB
    · simpa using lift 2 C hC
    · simpa using lift 3 D hD
  -- step 5: `S - 1` kills the `3^k`-torsion
  intro v hv
  obtain ⟨α, rfl⟩ := hsurj v
  have hα : (3 : R k) ^ k • α = 0 := hinj0 _ (by rw [φ_smul]; exact hv)
  have hNv : S (φ I J x α) - φ I J x α = 0 := by
    rw [hSφ, ← φ_sub_left, ← ha, ha', φ_smul, φ_smul_left, hα, φ_zero]
  exact sub_eq_zero.mp hNv

end Core


/-! ## 4. Transport from a commutative group with `G[3^{2k}] ≅ (ℤ/3^{2k})⁴` -/

section Transport

variable {G : Type*} [CommGroup G] {q : ℕ} {M : Type*} [AddCommGroup M]
  (e : {x : G | x ^ q = 1} ≃ M)

open Classical in
/-- `e` extended by `0` off the `q`-torsion. -/
noncomputable def E (g : G) : M := if h : g ^ q = 1 then e ⟨g, h⟩ else 0

lemma E_mem (g : G) (h : g ^ q = 1) : E e g = e ⟨g, h⟩ := by
  simp only [E, h, dite_true]

lemma E_symm (v : M) : E e (e.symm v).1 = v := by
  rw [E_mem e _ (e.symm v).2]; simp

lemma symm_E (g : G) (h : g ^ q = 1) : (e.symm (E e g)).1 = g := by
  rw [E_mem e g h, Equiv.symm_apply_apply]

lemma E_inj (a b : G) (ha : a ^ q = 1) (hb : b ^ q = 1) (h : E e a = E e b) : a = b := by
  rw [E_mem e a ha, E_mem e b hb] at h
  exact congrArg Subtype.val (e.injective h)

lemma mem_map (f : G →* G) (a : G) (ha : a ^ q = 1) : (f a) ^ q = 1 := by
  rw [← map_pow, ha, map_one]

lemma mem_mul (a b : G) (ha : a ^ q = 1) (hb : b ^ q = 1) : (a * b) ^ q = 1 := by
  rw [mul_pow, ha, hb, one_mul]

lemma mem_inv (a : G) (ha : a ^ q = 1) : a⁻¹ ^ q = 1 := by
  rw [inv_pow, ha, inv_one]

lemma mem_pow (a : G) (ha : a ^ q = 1) (n : ℕ) : (a ^ n) ^ q = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]

variable {e}
variable (he : ∀ x y : {x : G | x ^ q = 1}, ∀ h : x.1 * y.1 ∈ {x : G | x ^ q = 1},
  e ⟨x.1 * y.1, h⟩ = e x + e y)
include he

lemma E_mul (a b : G) (ha : a ^ q = 1) (hb : b ^ q = 1) : E e (a * b) = E e a + E e b := by
  rw [E_mem e _ (mem_mul a b ha hb), E_mem e _ ha, E_mem e _ hb]
  exact he ⟨a, ha⟩ ⟨b, hb⟩ (mem_mul a b ha hb)

lemma E_one : E e (1 : G) = 0 := by
  have h := E_mul he 1 1 (one_pow _) (one_pow _)
  rw [mul_one] at h
  simpa using h

lemma E_inv (a : G) (ha : a ^ q = 1) : E e a⁻¹ = -E e a := by
  have h := E_mul he a⁻¹ a (mem_inv a ha) ha
  rw [inv_mul_cancel, E_one he] at h
  exact eq_neg_of_add_eq_zero_left h.symm

lemma E_pow (a : G) (ha : a ^ q = 1) (n : ℕ) : E e (a ^ n) = n • E e a := by
  induction n with
  | zero => rw [pow_zero, E_one he, zero_smul]
  | succ n ih => rw [pow_succ, E_mul he _ _ (mem_pow a ha n) ha, ih, succ_nsmul]

/-- A group endomorphism, transported to an additive endomorphism of `M`. -/
noncomputable def endV (f : G →* G) : M →+ M where
  toFun v := E e (f (e.symm v).1)
  map_zero' := by
    rw [← E_one he, symm_E e 1 (one_pow _), map_one]
  map_add' v w := by
    have ha := (e.symm v).2
    have hb := (e.symm w).2
    have h1 : v + w = E e ((e.symm v).1 * (e.symm w).1) := by
      rw [E_mul he _ _ ha hb, E_symm, E_symm]
    show E e (f (e.symm (v + w)).1) = E e (f (e.symm v).1) + E e (f (e.symm w).1)
    rw [h1, symm_E e _ (mem_mul _ _ ha hb), map_mul,
      E_mul he _ _ (mem_map f _ ha) (mem_map f _ hb)]

lemma endV_E (f : G →* G) (g : G) (hg : g ^ q = 1) : endV he f (E e g) = E e (f g) := by
  show E e (f (e.symm (E e g)).1) = _
  rw [symm_E e g hg]

end Transport

/-- `QuatUnipotentTrivial`, verbatim from scratch/rv-a6-route/A6.lean §10. -/
def QuatUnipotentTrivial : Prop :=
  ∀ (G : Type u) [CommGroup G] (k : ℕ), 1 ≤ k → ∀ (I J S : G →* G),
    (∀ x, I (I x) = x ^ 2) → (∀ x, J (J x) * x ^ 3 = 1) → (∀ x, J (I x) * I (J x) = 1) →
    (∀ x, S (I x) = I (S x)) → (∀ x, S (J x) = J (S x)) →
    (∃ e : {x : G | x ^ (3 ^ (2 * k)) = 1} ≃ (Fin (2 * 2) → ZMod (3 ^ (2 * k))),
      ∀ x y : {x : G | x ^ (3 ^ (2 * k)) = 1},
        ∀ h : x.1 * y.1 ∈ {x : G | x ^ (3 ^ (2 * k)) = 1}, e ⟨x.1 * y.1, h⟩ = e x + e y) →
    (∀ x, x ^ (3 ^ (2 * k)) = 1 → S (S x) * (S x)⁻¹ * (S x)⁻¹ * x = 1) →
    ∀ x, x ^ (3 ^ k) = 1 → S x = x

/-- **`QuatUnipotentTrivial` (proved).** -/
theorem quatUnipotentTrivial : QuatUnipotentTrivial.{u} := by
  intro G _ k hk I J S hI hJ hIJ hSI hSJ ⟨e₀, he₀⟩ hS x hx
  let e : {x : G | x ^ (Q k) = 1} ≃ V k := e₀
  have he : ∀ x y : {x : G | x ^ (Q k) = 1}, ∀ h : x.1 * y.1 ∈ {x : G | x ^ (Q k) = 1},
      e ⟨x.1 * y.1, h⟩ = e x + e y := he₀
  -- every `v` is `E a` with `a ∈ G[q]`
  have hv : ∀ v : V k, ∃ a : G, a ^ (Q k) = 1 ∧ E e a = v :=
    fun v => ⟨_, (e.symm v).2, E_symm e v⟩
  let IV := (endV he I).toZModLinearMap (Q k)
  let JV := (endV he J).toZModLinearMap (Q k)
  let SV := (endV he S).toZModLinearMap (Q k)
  have hIV : ∀ g, g ^ (Q k) = 1 → IV (E e g) = E e (I g) := fun g hg => endV_E he I g hg
  have hJV : ∀ g, g ^ (Q k) = 1 → JV (E e g) = E e (J g) := fun g hg => endV_E he J g hg
  have hSV : ∀ g, g ^ (Q k) = 1 → SV (E e g) = E e (S g) := fun g hg => endV_E he S g hg
  have mI := mem_map (q := Q k) I
  have mJ := mem_map (q := Q k) J
  have mS := mem_map (q := Q k) S
  have key := core hk IV JV SV
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hIV a ha, hIV _ (mI a ha), hI, E_pow he a ha, two_smul, two_smul])
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hJV a ha, hJV _ (mJ a ha)]
      have h := congrArg (E e) (hJ a)
      rw [E_mul he _ _ (mJ _ (mJ a ha)) (mem_pow a ha 3), E_pow he a ha, E_one he] at h
      rw [neg_smul, ofNat_smul_eq_nsmul]
      exact eq_neg_of_add_eq_zero_left h)
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hIV a ha, hJV _ (mI a ha), hJV a ha, hIV _ (mJ a ha)]
      have h := congrArg (E e) (hIJ a)
      rw [E_mul he _ _ (mJ _ (mI a ha)) (mI _ (mJ a ha)), E_one he] at h
      exact eq_neg_of_add_eq_zero_left h)
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hIV a ha, hSV _ (mI a ha), hSV a ha, hIV _ (mS a ha), hSI])
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hJV a ha, hSV _ (mJ a ha), hSV a ha, hJV _ (mS a ha), hSJ])
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hSV a ha, hSV _ (mS a ha)]
      have h := congrArg (E e) (hS a ha)
      have m1 := mS _ (mS a ha)
      have m2 := mem_inv _ (mS a ha)
      rw [E_mul he _ _ (mem_mul _ _ (mem_mul _ _ m1 m2) m2) ha,
        E_mul he _ _ (mem_mul _ _ m1 m2) m2, E_mul he _ _ m1 m2, E_inv he _ (mS a ha),
        E_one he] at h
      rw [← h]; module)
  have hxq : x ^ (Q k) = 1 := by
    show x ^ (3 ^ (2 * k)) = 1
    rw [two_mul, pow_add, pow_mul, hx, one_pow]
  have h3 : (3 : R k) ^ k • E e x = 0 := by
    have : (3 : R k) ^ k = ((3 ^ k : ℕ) : R k) := by push_cast; rfl
    rw [this, Nat.cast_smul_eq_nsmul, ← E_pow he x hxq, hx, E_one he]
  have := key (E e x) h3
  rw [hSV x hxq] at this
  exact E_inj e _ _ (mS x hxq) hxq this

end GlueA6Alg


#print axioms GlueA6Alg.core
#print axioms GlueA6Alg.quatUnipotentTrivial

open Lean Elab Command in
elab "#rvw17_check_axioms" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut cnt : Nat := 0
  for (n, _) in env.constants.map₂.toList do
    if n.isInternal then continue
    cnt := cnt + 1
    let axs ← liftCoreM (Lean.collectAxioms n)
    if axs.any (fun a => a ∉ [``propext, ``Classical.choice, ``Quot.sound]) then
      bad := bad.push n
      logInfo m!"BAD {n}: {axs}"
  logInfo m!"rvw17: {cnt} declarations checked, {bad.size} with nonstandard axioms"

#rvw17_check_axioms
