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

/-- `κ` as a `ℤ`-algebra map. -/
def kappaZ (m : ℕ) : QNeg m →ₐ[ℤ] ℂ := (kappaAlg m).restrictScalars ℤ

/-- `κ` as a `ℤ`-linear map. -/
def kappaLin (m : ℕ) : QNeg m →ₗ[ℤ] ℂ := (kappaZ m).toLinearMap

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



section X0Id
open WeierstrassCurve.Affine

theorem curveAC_a₁ : X0.curveAC.a₁ = 0 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
theorem curveAC_a₃ : X0.curveAC.a₃ = 0 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]

theorem negY_AC (x y : ℂ) : X0.curveAC.toAffine.negY x y = -y := by
  rw [negY, curveAC_a₁, curveAC_a₃]; ring

/-- **`φ(τ + 1/2) = −φ(τ)`** (from x0-32's `xC_add_half`, `yC_add_half`). -/
theorem phiC_add_half (τ τ' : UpperHalfPlane) (h : (τ' : ℂ) = τ + 1 / 2) :
    X0.phiC τ' = -X0.phiC τ := by
  have hx : X0.xC τ' = X0.xC τ := by rw [h, X0.xC_add_half]
  have hy : X0.yC τ' = -X0.yC τ := by rw [h, X0.yC_add_half]
  unfold X0.phiC
  by_cases hns : X0.curveAC.toAffine.Nonsingular (X0.xC τ) (X0.yC τ)
  · have hns' : X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [hx, hy, ← negY_AC]; exact (nonsingular_neg ..).2 hns
    rw [dite_eq_left hns, dite_eq_left hns', Point.neg_some, Point.some.injEq, negY_AC]
    exact ⟨hx, hy⟩
  · have hns' : ¬ X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [hx, hy, ← negY_AC]; exact fun h' => hns ((nonsingular_neg ..).1 h')
    rw [dite_eq_right hns, dite_eq_right hns', neg_zero]

/-- `(0, 0) ∈ A(ℂ)`. -/
theorem nonsingular_00C : X0.curveAC.toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff']
  have h4 : X0.curveAC.a₄ = 4 := by simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
  have h0 : X0.curveAC.a₂ = 0 ∧ X0.curveAC.a₆ = 0 := by
    simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
  rw [h4, curveAC_a₁, curveAC_a₃, h0.1, h0.2]
  refine ⟨by norm_num, Or.inl ?_⟩
  norm_num

def pt00C : X0.PtAC := .some 0 0 nonsingular_00C

theorem ptTC_add_self : X0.ptTC + X0.ptTC = pt00C := by
  have hy : (-4 : ℂ) ≠ X0.curveAC.toAffine.negY 2 (-4) := by rw [negY_AC]; norm_num
  rw [X0.ptTC, Point.add_self_of_Y_ne hy, pt00C, Point.some.injEq]
  have h4 : X0.curveAC.a₄ = 4 := by simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
  have h2 : X0.curveAC.a₂ = 0 := by simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
  have hs : X0.curveAC.toAffine.slope 2 2 (-4) (-4) = -2 := by
    rw [slope_of_Y_ne rfl hy]
    simp only [negY, curveAC_a₁, curveAC_a₃, h2, h4]; norm_num
  simp only [addX, addY, negAddY, negY, hs, curveAC_a₁, h2, curveAC_a₃]
  constructor <;> norm_num

theorem neg_pt00C : -pt00C = pt00C := by
  rw [pt00C, Point.neg_some, Point.some.injEq, negY_AC]; simp

/-- `τ ↦ −1/(32τ)` on `ℍ`. -/
def frickeH (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨-1 / (32 * (τ : ℂ)), by
    have h32 : (32 : ℂ) * τ = ((32 : ℕ) : ℂ) * τ := by norm_num
    have hm := X0.mul_mem_upperHalfPlaneSet (d := 32) (by norm_num) τ
    rw [← h32] at hm
    have := UpperHalfPlane.im_inv_neg_coe_pos ⟨_, hm⟩
    simpa [div_eq_mul_inv, neg_inv] using this⟩

/-- `τ ↦ τ + 1/2` on `ℍ`. -/
def halfH (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(τ : ℂ) + 1 / 2, by
    show 0 < ((τ : ℂ) + 1 / 2).im
    simpa using τ.im_pos⟩

/-- **`φ(N₀τ) = φ(τ) + (0, 0)`** for `N₀ = S W S W`, `N₀τ = (14τ − 1)/(32τ − 2)`, from the Fricke
leaf `X0.EtaModelFricke` (`φ(Wτ) = T − φ(τ)`) and `φ(τ + 1/2) = −φ(τ)`; `2T = (0,0)`. -/
theorem phiC_N0 (hF : X0.EtaModelFricke) (τ τ' : UpperHalfPlane)
    (h : (τ' : ℂ) = (14 * τ - 1) / (32 * τ - 2)) : X0.phiC τ' = X0.phiC τ + pt00C := by
  set τ₁ := frickeH τ
  set τ₂ := halfH τ₁
  set τ₃ := frickeH τ₂
  have hτ' : (τ' : ℂ) = (halfH τ₃ : ℂ) := by
    rw [h]
    show _ = -1 / (32 * ((-1 / (32 * (τ : ℂ))) + 1 / 2)) + 1 / 2
    have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
    have hτ1 : (16 * (τ : ℂ) - 1) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      exact τ.im_pos.ne' this
    have hτ2 : (32 * (τ : ℂ) - 2) ≠ 0 := by
      intro h0; apply hτ1; linear_combination h0 / 2
    have hτ3 : (-2 + (τ : ℂ) * 32) ≠ 0 := by
      intro h0; apply hτ2; linear_combination h0
    field_simp
    ring_nf
    field_simp
    ring
  have e1 : X0.phiC τ₁ + X0.phiC τ = X0.ptTC := hF τ τ₁ rfl
  have e2 : X0.phiC τ₂ = -X0.phiC τ₁ := phiC_add_half τ₁ τ₂ rfl
  have e3 : X0.phiC τ₃ + X0.phiC τ₂ = X0.ptTC := hF τ₂ τ₃ rfl
  have e4 : X0.phiC τ' = -X0.phiC τ₃ := phiC_add_half τ₃ τ' hτ'
  rw [e4, eq_sub_of_add_eq e3, e2, eq_sub_of_add_eq e1]
  rw [← neg_pt00C, ← ptTC_add_self]
  abel

end X0Id

section Assembly
open QuadraticAlgebra Pointwise WeierstrassCurve.Affine

/-- **`Q'_n = [16(n+9), −8(2n+15), 4n+25]`**, a Heegner form of level 32 and discriminant `−64n`
(`n ≡ 5 mod 8`), with `τ_{Q'} = N₀ τ_{Q_n}` (`tau'_eq`) and lattice pair `𝔟⁻¹`-homothetic to that of
TYZ's form `Q_n` (`idealLat_alpha_mul`, `idealLat_alpha_mulN`). -/
def tyzForm' (n : ℕ) (hn : n % 8 = 5) : HeegnerForm 32 (-64 * n) where
  A := 16 * (n + 9)
  B := -8 * (2 * n + 15)
  C := 4 * n + 25
  A_pos := by positivity
  N_dvd := by
    have : (n : ℤ) % 8 = 5 := by exact_mod_cast hn
    omega
  disc := by ring
  D_neg := by
    have : (0 : ℤ) < n := by omega
    linarith
  primitive := by
    have hA : ((Int.gcd (Int.gcd (16 * ((n : ℤ) + 9)) (-8 * (2 * n + 15))) (4 * n + 25) : ℕ) : ℤ) ∣
        16 * ((n : ℤ) + 9) := (Int.gcd_dvd_left ..).trans (Int.gcd_dvd_left ..)
    have hB : ((Int.gcd (Int.gcd (16 * ((n : ℤ) + 9)) (-8 * (2 * n + 15))) (4 * n + 25) : ℕ) : ℤ) ∣
        -8 * (2 * n + 15) := (Int.gcd_dvd_left ..).trans (Int.gcd_dvd_right ..)
    have hC : ((Int.gcd (Int.gcd (16 * ((n : ℤ) + 9)) (-8 * (2 * n + 15))) (4 * n + 25) : ℕ) : ℤ) ∣
        4 * n + 25 := Int.gcd_dvd_right ..
    have h1 : ((Int.gcd (Int.gcd (16 * ((n : ℤ) + 9)) (-8 * (2 * n + 15))) (4 * n + 25) : ℕ) : ℤ) ∣
        1 := by
      have e : (1 : ℤ) = -(n + 6) * (16 * (n + 9)) - 2 * (n + 6) * (-8 * (2 * n + 15)) +
          (-4 * n - 23) * (4 * n + 25) := by ring
      rw [e]
      exact dvd_add (dvd_sub (dvd_mul_of_dvd_right hA _) (dvd_mul_of_dvd_right hB _))
        (dvd_mul_of_dvd_right hC _)
    exact Nat.dvd_one.mp (by exact_mod_cast h1)

theorem sqrt_64n (n : ℕ) : Real.sqrt (-(((-64 * n : ℤ)) : ℝ)) = 8 * Real.sqrt n := by
  rw [show -(((-64 * n : ℤ)) : ℝ) = 8 ^ 2 * n by push_cast; ring,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

theorem tyzForm_tau (n : ℕ) (hn : n % 8 = 5) : (tyzForm n hn).tau = kappa n (tauK n) := by
  have h1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [HeegnerForm.tau, cmPoint, tyzForm, kappa, tauK, sqrt_64n]
  push_cast
  field_simp
  ring

theorem tyzForm'_tau (n : ℕ) (hn : n % 8 = 5) : (tyzForm' n hn).tau = kappa n (tauK' n) := by
  have h9 : ((n : ℂ) + 9) ≠ 0 := by exact_mod_cast (show n + 9 ≠ 0 by omega)
  simp only [HeegnerForm.tau, cmPoint, tyzForm', kappa, tauK', sqrt_64n]
  push_cast
  field_simp
  ring

theorem tauK'_mul (n : ℕ) [NeZero n] : tauK' n * (32 * tauK n - 2) = 14 * tauK n - 1 := by
  have h1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have h9 : ((n : ℚ) + 9) ≠ 0 := by positivity
  ext <;> simp [tauK, tauK'] <;> field_simp <;> ring

theorem tau'_eq (n : ℕ) [NeZero n] (hn : n % 8 = 5) :
    ((tyzForm' n hn).tauH : ℂ) = (14 * ((tyzForm n hn).tauH : ℂ) - 1) / (32 * (tyzForm n hn).tauH - 2) := by
  have hτ : ((tyzForm n hn).tauH : ℂ) = kappaAlg n (tauK n) := by
    rw [kappaAlg_apply, ← tyzForm_tau n hn]; rfl
  have hτ' : ((tyzForm' n hn).tauH : ℂ) = kappaAlg n (tauK' n) := by
    rw [kappaAlg_apply, ← tyzForm'_tau n hn]; rfl
  have hne : (32 * ((tyzForm n hn).tauH : ℂ) - 2) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact (tyzForm n hn).tauH.im_pos.ne' this
  rw [eq_div_iff hne, hτ', hτ]
  have := congrArg (kappaAlg n) (tauK'_mul n)
  simpa [map_ofNat] using this

theorem kappaLin_one (n : ℕ) : kappaLin n 1 = 1 := map_one (kappaZ n)

theorem kappa_oneN (n : ℕ) : kappaLin n (oneN n) = 1 / ((32 : ℕ) : ℂ) := by
  rw [kappaLin_apply, kappa]; simp

theorem lat_eq_map {D : ℤ} (Q : HeegnerForm 32 D) (n : ℕ) (t : QNeg n) (ht : Q.tau = kappa n t) :
    Q.lat = (Submodule.span ℤ {1, t}).map (kappaLin n) := by
  rw [HeegnerForm.lat, Submodule.map_span, Set.image_pair, kappaLin_one, kappaLin_apply, ht]

theorem latN_eq_map {D : ℤ} (Q : HeegnerForm 32 D) (n : ℕ) (t : QNeg n) (ht : Q.tau = kappa n t) :
    Q.latN = (Submodule.span ℤ {oneN n, t}).map (kappaLin n) := by
  rw [HeegnerForm.latN, Submodule.map_span, Set.image_pair, kappa_oneN, kappaLin_apply, ht]

theorem map_mulLeft_span_pair (n : ℕ) (c a b : QNeg n) :
    ((Submodule.span ℤ {a, b}).map (kappaLin n)).map (LinearMap.mulLeft ℤ (kappa n c)) =
      (Submodule.span ℤ {c * a, c * b}).map (kappaLin n) := by
  simp only [Submodule.map_span, Set.image_pair, LinearMap.mulLeft_apply, kappaLin_apply]
  rw [← kappaAlg_apply, ← kappaAlg_apply, ← kappaAlg_apply, ← kappaAlg_apply, ← kappaAlg_apply,
    map_mul, map_mul]

theorem idealLat_alpha (n : ℕ) [NeZero n] (hn : n % 4 = 1) (hsq : Squarefree n) :
    idealLat n 4 (Ideal.span {alpha n}) = (Submodule.span ℤ {g0 n, g1 n}).map (kappaLin n) := by
  rw [idealLat, idealMeetOrder_alpha hn hsq, show kappa n = kappaLin n from funext fun x => (kappaLin_apply n x).symm,
    Submodule.span_image, Submodule.span_eq]

theorem idealLat_alpha_mul (n : ℕ) [NeZero n] (hn : n % 8 = 5) (hsq : Squarefree n) :
    idealLat n 4 (Ideal.span {alpha n}) * (tyzForm' n hn).lat =
      (tyzForm n hn).lat.map (LinearMap.mulLeft ℤ (kappa n (cK n))) := by
  rw [idealLat_alpha n (by omega) hsq, lat_eq_map _ n _ (tyzForm'_tau n hn),
    lat_eq_map _ n _ (tyzForm_tau n hn), map_mulLeft_span_pair, kappaLin, ← Submodule.map_mul,
    latK (n / 8) (by omega)]

theorem idealLat_alpha_mulN (n : ℕ) [NeZero n] (hn : n % 8 = 5) (hsq : Squarefree n) :
    idealLat n 4 (Ideal.span {alpha n}) * (tyzForm' n hn).latN =
      (tyzForm n hn).latN.map (LinearMap.mulLeft ℤ (kappa n (cK n))) := by
  rw [idealLat_alpha n (by omega) hsq, latN_eq_map _ n _ (tyzForm'_tau n hn),
    latN_eq_map _ n _ (tyzForm_tau n hn), map_mulLeft_span_pair, kappaLin, ← Submodule.map_mul,
    latNK (n / 8) (by omega)]

end Assembly

end ZInQ.Contrib.TYZGenus.Shimura
