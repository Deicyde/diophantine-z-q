import ZInQKernel.Contrib.TYZGenus.ShimuraRecip

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex

theorem sqrt_mul_self_C (m : ℕ) : (Real.sqrt m : ℂ) * Real.sqrt m = m := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg m)]; simp

/-- `i√m` as a root of `X² + m` in `ℂ`. -/
def kappaRoot (m : ℕ) : {u : ℂ // u * u = (-(m : ℚ)) • (1 : ℂ) + (0 : ℚ) • u} :=
  ⟨I * Real.sqrt m, by
    rw [show I * (Real.sqrt m : ℂ) * (I * Real.sqrt m) = (I * I) * (Real.sqrt m * Real.sqrt m) by ring,
      I_mul_I, sqrt_mul_self_C]
    simp [Rat.smul_def]⟩

/-- `κ` as a `ℚ`-algebra map. -/
def kappaAlg (m : ℕ) : QNeg m →ₐ[ℚ] ℂ := QuadraticAlgebra.lift (kappaRoot m)

theorem kappaAlg_apply (m : ℕ) (x : QNeg m) : kappaAlg m x = kappa m x := by
  simp [kappaAlg, kappa, kappaRoot, Rat.smul_def]

/-- `κ` as a `ℤ`-linear map. -/
def kappaLin (m : ℕ) : QNeg m →ₗ[ℤ] ℂ := (kappaAlg m).toLinearMap.restrictScalars ℤ

theorem kappaLin_apply (m : ℕ) (x : QNeg m) : kappaLin m x = kappa m x := kappaAlg_apply m x

/-! ### Integer coordinates in `𝓞_K` for `n ≡ 1 (mod 4)` squarefree -/

theorem int_coords {n : ℕ} [NeZero n] (hn : n % 4 = 1) (hsq : Squarefree n) (y : 𝓞 (QNeg n)) :
    ∃ u v : ℤ, (y : QNeg n).re = u ∧ (y : QNeg n).im = v := by
  obtain ⟨a, ha⟩ := exists_two_re y
  obtain ⟨b, hb⟩ := exists_two_re (y * sqrtNeg n)
  have hN := normZ_eq_re_im y
  set N := Algebra.norm ℤ y
  set r := (y : QNeg n).re
  set s := (y : QNeg n).im
  have hb' : 2 * (-(n : ℚ) * s) = b := by
    rw [← hb]; simp [coe_sqrtNeg, s]
  -- t = 2s, n t = -b
  have hnt : (n : ℚ) * (2 * s) = -b := by linarith
  have h4 : (a : ℚ) ^ 2 + n * (2 * s) ^ 2 = 4 * N := by
    rw [hN, ← ha]; ring
  have hdiv : (n : ℤ) ∣ b ^ 2 := by
    refine ⟨a ^ 2 * 0 + (4 * N - a ^ 2), ?_⟩
    have : (b : ℚ) ^ 2 = n * (4 * N - a ^ 2) := by
      have : (b : ℚ) ^ 2 = (n * (2 * s)) ^ 2 := by rw [hnt]; ring
      rw [this]; linear_combination (n : ℚ) * h4
    exact_mod_cast (by rw [this]; ring : (b : ℚ) ^ 2 = n * (a ^ 2 * 0 + (4 * N - a ^ 2)))
  have hsqZ : Squarefree (n : ℤ) := Int.squarefree_natCast.mpr hsq
  obtain ⟨t, ht⟩ := (hsqZ.dvd_pow_iff_dvd two_ne_zero).1 hdiv
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hs2 : 2 * s = -t := by
    have : (n : ℚ) * (2 * s) = n * (-t) := by rw [hnt, ht]; push_cast; ring
    exact mul_left_cancel₀ hn0 this
  have hZ : a ^ 2 + (n : ℤ) * t ^ 2 = 4 * N := by
    have : (a : ℚ) ^ 2 + n * t ^ 2 = 4 * N := by rw [← h4, hs2]; ring
    exact_mod_cast this
  have hn4 : (n : ℤ) % 4 = 1 := by exact_mod_cast hn
  have hat : 2 ∣ a ∧ 2 ∣ t := by
    have hm : ∀ x : ℤ, x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
      intro x; rcases Int.emod_two_eq_zero_or_one x with h | h
      · left; obtain ⟨k, rfl⟩ : 2 ∣ x := Int.dvd_of_emod_eq_zero h; ring_nf; omega
      · right; obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
        subst hk; ring_nf; omega
    have hpar : ∀ x : ℤ, x ^ 2 % 4 = 0 → 2 ∣ x := by
      intro x hx; by_contra h
      obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
      subst hk; ring_nf at hx; omega
    have e1 : ((n : ℤ) * t ^ 2) % 4 = (t ^ 2) % 4 := by
      rw [Int.mul_emod, hn4, one_mul, Int.emod_emod_of_dvd _ (by norm_num)]
    have e2 : (a ^ 2 + (n : ℤ) * t ^ 2) % 4 = 0 := by rw [hZ]; simp
    rcases hm a with h1 | h1 <;> rcases hm t with h2 | h2
    · exact ⟨hpar a h1, hpar t h2⟩
    · omega
    · omega
    · omega
  obtain ⟨⟨a', rfl⟩, ⟨t', rfl⟩⟩ := hat
  refine ⟨a', -t', ?_, ?_⟩
  · have : 2 * r = 2 * a' := by rw [ha]; push_cast; ring
    linarith
  · have : 2 * s = 2 * (-t') := by rw [hs2]; push_cast; ring
    push_cast; linarith


/-! ### `𝔟 ∩ O_{n,4}` for `𝔟 = (3 + 2√−n)` -/

section Alpha
open QuadraticAlgebra
variable {n : ℕ} [NeZero n]

/-- `6 + 4√−n = 2α`. -/
def g0 (n : ℕ) : QNeg n := ⟨6, 4⟩
/-- `3 − 4n + 8√−n = α(1 + 2√−n)`. -/
def g1 (n : ℕ) : QNeg n := ⟨3 - 4 * n, 8⟩

theorem coeO_two : ((2 : 𝓞 (QNeg n)) : QNeg n) = 2 := rfl
theorem coeO_three : ((3 : 𝓞 (QNeg n)) : QNeg n) = 3 := rfl

theorem coe_alpha : ((alpha n : 𝓞 (QNeg n)) : QNeg n) = ⟨3, 2⟩ := by
  rw [alpha]; push_cast [coe_sqrtNeg, coeO_two, coeO_three]; ext <;> simp

theorem mem_O4_iff' (x : QNeg n) :
    x ∈ (conductorOrder (QNeg n) 4).toSubalgebra ↔ ∃ a : ℤ, ∃ y : 𝓞 (QNeg n), x = a + 4 * (y : QNeg n) := by
  rw [conductorOrder_toSubalgebra, mem_conductorOrderSubalgebra]; norm_num

theorem idealMeetOrder_alpha (hn : n % 4 = 1) (hsq : Squarefree n) :
    idealMeetOrder n 4 (Ideal.span {alpha n}) =
      (Submodule.span ℤ ({g0 n, g1 n} : Set (QNeg n)) : Set (QNeg n)) := by
  ext x
  simp only [idealMeetOrder, Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_span_pair, mem_O4_iff']
  constructor
  · rintro ⟨⟨a, z, hz⟩, y, hy, rfl⟩
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨u, v, hu, hv⟩ := int_coords hn hsq w
    obtain ⟨p, q, hp, hq⟩ := int_coords hn hsq z
    have him := congrArg QuadraticAlgebra.im hz
    push_cast [coe_alpha] at him
    simp only [im_mul, hu, hv, im_add, im_intCast, im_mul, hp, hq] at him
    simp at him
    have h4 : 2 * u + 3 * v = 4 * q := by
      have : (2 * u + 3 * v : ℚ) = 4 * q := by linarith
      exact_mod_cast this
    refine ⟨q - v, 2 * q - u - v, ?_⟩
    push_cast [coe_alpha]
    ext
    · simp [g0, g1, hu, hv]
      have : (2 * u + 3 * v : ℚ) = 4 * q := by exact_mod_cast h4
      linear_combination (2 * (n : ℚ) - 3) * this
    · simp [g0, g1, hu, hv]
      have : (2 * u + 3 * v : ℚ) = 4 * q := by exact_mod_cast h4
      linear_combination (-5 : ℚ) * this
  · rintro ⟨c, d, rfl⟩
    refine ⟨⟨6 * c + d * (3 - 4 * n), (c + 2 * d : ℤ) * sqrtNeg n, ?_⟩,
      (2 * c + d + 2 * d * sqrtNeg n : 𝓞 (QNeg n)) * alpha n,
      Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), ?_⟩
    · push_cast [coe_sqrtNeg, coeO_two]; ext <;> simp [g0, g1] <;> ring
    · push_cast [coe_sqrtNeg, coe_alpha, coeO_two]; ext <;> simp [g0, g1] <;> ring

end Alpha

/-! ### The lattice identity in `K` -/

section LatK
open QuadraticAlgebra Pointwise
variable {n : ℕ} [NeZero n]

/-- `τ_Q = (1 + √−n)/(4(n+1))` for TYZ's form `[16(n+1), −8, 1]`. -/
def tauK (n : ℕ) : QNeg n := ⟨1 / (4 * (n + 1)), 1 / (4 * (n + 1))⟩
/-- `τ_{Q'} = (2n + 15 + √−n)/(4(n+9))` for `Q' = [16(n+9), −8(2n+15), 4n+25]`. -/
def tauK' (n : ℕ) : QNeg n := ⟨(2 * n + 15) / (4 * (n + 9)), 1 / (4 * (n + 9))⟩
/-- `1/32 ∈ K`. -/
def oneN (n : ℕ) : QNeg n := ⟨1 / 32, 0⟩
omit [NeZero n] in
@[simp] theorem oneN_re : (oneN n).re = 1 / 32 := rfl
omit [NeZero n] in
@[simp] theorem oneN_im : (oneN n).im = 0 := rfl
/-- The homothety factor `c = ((5n+9) − 2(n+3)√−n)/(n+9)`. -/
def cK (n : ℕ) : QNeg n := ⟨(5 * n + 9) / (n + 9), -2 * (n + 3) / (n + 9)⟩

omit [NeZero n] in
theorem mem_span_mul_four {S T : Set (QNeg n)} (s₀ s₁ t₀ t₁ : QNeg n) (hs₀ : s₀ ∈ S) (hs₁ : s₁ ∈ S)
    (ht₀ : t₀ ∈ T) (ht₁ : t₁ ∈ T) {x : QNeg n} (a b c d : ℤ)
    (h : x = a • (s₀ * t₀) + b • (s₀ * t₁) + c • (s₁ * t₀) + d • (s₁ * t₁)) :
    x ∈ Submodule.span ℤ (S * T) := by
  rw [h]
  have hm : ∀ {s t : QNeg n}, s ∈ S → t ∈ T → s * t ∈ Submodule.span ℤ (S * T) :=
    fun hs ht => Submodule.subset_span (Set.mul_mem_mul hs ht)
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (hm hs₀ ht₀)) (Submodule.smul_mem _ _ (hm hs₀ ht₁)))
    (Submodule.smul_mem _ _ (hm hs₁ ht₀))) (Submodule.smul_mem _ _ (hm hs₁ ht₁))

omit [NeZero n] in
theorem mem_span_pair_of {a b x : QNeg n} (p q : ℤ) (h : x = p • a + q • b) :
    x ∈ Submodule.span ℤ ({a, b} : Set (QNeg n)) :=
  Submodule.mem_span_pair.2 ⟨p, q, h.symm⟩

theorem latK (k : ℕ) (hk : n = 8 * k + 5) :
    Submodule.span ℤ ({g0 n, g1 n} : Set (QNeg n)) * Submodule.span ℤ {1, tauK' n} =
      Submodule.span ℤ {cK n * 1, cK n * tauK n} := by
  subst hk
  have h1 : (8 * (k : ℚ) + 5 + 1) ≠ 0 := by positivity
  have h9 : (8 * (k : ℚ) + 5 + 9) ≠ 0 := by positivity
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact mem_span_pair_of (-2) 32 (by ext <;> simp [g0, cK, tauK] <;> field_simp <;> ring)
    · exact mem_span_pair_of (-1) 14 (by ext <;> simp [g0, cK, tauK, tauK'] <;> field_simp <;> ring)
    · exact mem_span_pair_of (-7) (-64 * k) (by ext <;> simp [g1, cK, tauK] <;> field_simp <;> ring)
    · exact mem_span_pair_of (-3) (-32 * k - 3)
        (by ext <;> simp [g1, cK, tauK, tauK'] <;> field_simp <;> ring)
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact mem_span_mul_four (g0 _) (g1 _) 1 (tauK' _) (by simp) (by simp) (by simp) (by simp)
        (-(112 * k + 70)) (256 * k + 160) (-32 * k - 3) (64 * k)
        (by ext <;> simp [g0, g1, cK, tauK'] <;> field_simp <;> ring)
    · exact mem_span_mul_four (g0 _) (g1 _) 1 (tauK' _) (by simp) (by simp) (by simp) (by simp)
        (-(8 * k + 5)) (16 * k + 10) 3 (-7)
        (by ext <;> simp [g0, g1, cK, tauK, tauK'] <;> field_simp <;> ring)

theorem latNK (k : ℕ) (hk : n = 8 * k + 5) :
    Submodule.span ℤ ({g0 n, g1 n} : Set (QNeg n)) * Submodule.span ℤ {oneN n, tauK' n} =
      Submodule.span ℤ {cK n * oneN n, cK n * tauK n} := by
  subst hk
  have h1 : (8 * (k : ℚ) + 5 + 1) ≠ 0 := by positivity
  have h9 : (8 * (k : ℚ) + 5 + 9) ≠ 0 := by positivity
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact mem_span_pair_of (-2) 1 (by ext <;> simp [g0, cK, tauK] <;> field_simp <;> ring)
    · exact mem_span_pair_of (-32) 14 (by ext <;> simp [g0, cK, tauK, tauK'] <;> field_simp <;> ring)
    · exact mem_span_pair_of (-7) (-2 * k) (by ext <;> simp [g1, cK, tauK] <;> field_simp <;> ring)
    · exact mem_span_pair_of (-96) (-32 * k - 3)
        (by ext <;> simp [g1, cK, tauK, tauK'] <;> field_simp <;> ring)
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact mem_span_mul_four (g0 _) (g1 _) (oneN _) (tauK' _) (by simp) (by simp) (by simp) (by simp)
        (-(112 * k + 70)) (8 * k + 5) (-32 * k - 3) (2 * k)
        (by ext <;> simp [g0, g1, cK, tauK'] <;> field_simp <;> ring)
    · exact mem_span_mul_four (g0 _) (g1 _) (oneN _) (tauK' _) (by simp) (by simp) (by simp) (by simp)
        (-(8 * k + 5) * 32) ((8 * k + 5) * 2) 96 (-7)
        (by ext <;> simp [g0, g1, cK, tauK, tauK'] <;> field_simp <;> ring)

end LatK

end ZInQ.Contrib.TYZGenus.Shimura
