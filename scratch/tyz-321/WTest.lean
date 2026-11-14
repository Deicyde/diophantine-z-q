import ZInQKernel.Contrib.TYZGenus.RingClassBridge
import ZInQKernel.Contrib.TYZGenus.ShimuraFricke

noncomputable section

namespace ZInQ.Contrib.TYZGenus.T321W

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass ZInQ.PropN NumberField
  TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZGenus.RingClassBridge

def varpiIdeal (d : ℕ) [NeZero d] : Ideal (𝓞 (QNeg d)) :=
  Ideal.span {(((d + 1) / 2 : ℕ) : 𝓞 (QNeg d)), sqrtNeg d - 1}

open Classical in
def wClass (d : ℕ) [NeZero d] : Pic (O4 d) :=
  if h : varpiIdeal d ∈ integralIdealsPrimeTo (O4 d).conductorModulus then (O4 d).picClass ⟨_, h⟩
  else 1

open QuadraticAlgebra Pointwise WeierstrassCurve.Affine Complex

variable {n : ℕ} [NeZero n]

def hW0 (n : ℕ) : QNeg n := ⟨((n : ℚ) + 1) / 2, 0⟩
def hW1 (n : ℕ) : QNeg n := ⟨-4, 4⟩

@[simp] theorem hW0_re : (hW0 n).re = ((n : ℚ) + 1) / 2 := rfl
@[simp] theorem hW0_im : (hW0 n).im = 0 := rfl
@[simp] theorem hW1_re : (hW1 n).re = -4 := rfl
@[simp] theorem hW1_im : (hW1 n).im = 4 := rfl

theorem natCast_m (hn : n % 8 = 5) : (((n + 1) / 2 : ℕ) : ℚ) = ((n : ℚ) + 1) / 2 := by
  have : (n + 1) / 2 * 2 = n + 1 := by omega
  have h' : (((n + 1) / 2 : ℕ) : ℚ) * 2 = (n : ℚ) + 1 := by exact_mod_cast this
  linarith

theorem coe_m (hn : n % 8 = 5) :
    (((((n + 1) / 2 : ℕ) : 𝓞 (QNeg n))) : QNeg n) = hW0 n := by
  have h2 : (((n + 1) / 2 : ℕ) : ℚ) = ((n : ℚ) + 1) / 2 := by
    have : (n + 1) / 2 * 2 = n + 1 := by omega
    have h' : (((n + 1) / 2 : ℕ) : ℚ) * 2 = (n : ℚ) + 1 := by exact_mod_cast this
    linarith
  rw [show ((((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) : QNeg n) = (((n + 1) / 2 : ℕ) : QNeg n) from
    map_natCast (algebraMap (𝓞 (QNeg n)) (QNeg n)) _]
  ext
  · rw [QuadraticAlgebra.re_natCast, h2]; rfl
  · rw [QuadraticAlgebra.im_natCast]; rfl

theorem varpiIdeal_mem (hn : n % 8 = 5) :
    varpiIdeal n ∈ integralIdealsPrimeTo (O4 n).conductorModulus := by
  rw [Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff_sup_eq_top,
    conductorModulus_finitePart]
  have key : (1 : 𝓞 (QNeg n)) = (-1) * (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) +
      4 * (((n + 3) / 8 : ℕ) : 𝓞 (QNeg n)) := by
    have h' : (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) + 1 = 4 * (((n + 3) / 8 : ℕ) : 𝓞 (QNeg n)) := by
      exact_mod_cast (show (n + 1) / 2 + 1 = 4 * ((n + 3) / 8) by omega)
    linear_combination h'
  refine ⟨?_, ?_⟩
  · intro h
    have hmem : (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) ∈ varpiIdeal n :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h, Ideal.mem_bot] at hmem
    have h2 := congrArg (fun x : 𝓞 (QNeg n) => ((x : QNeg n)).re) hmem
    simp only [coe_m hn, hW0] at h2
    simp at h2
    have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    linarith
  · rw [Ideal.eq_top_iff_one, key]
    refine Ideal.add_mem _ (Ideal.mem_sup_left
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))) (Ideal.mem_sup_right ?_)
    simpa using natCast_mul_mem_conductor (QNeg n) 4 ((((n + 3) / 8 : ℕ)) : 𝓞 (QNeg n))

theorem idealMeetOrder_varpi (hn : n % 8 = 5) (hsq : Squarefree n) :
    Shimura.idealMeetOrder n 4 (varpiIdeal n) =
      (Submodule.span ℤ ({hW0 n, hW1 n} : Set (QNeg n)) : Set (QNeg n)) := by
  have hn4 : n % 4 = 1 := by omega
  have hmq := natCast_m hn
  unfold varpiIdeal
  generalize (n + 1) / 2 = m at hmq ⊢
  have hcm : ((m : 𝓞 (QNeg n)) : QNeg n) = hW0 n := by
    rw [show ((m : 𝓞 (QNeg n)) : QNeg n) = (m : QNeg n) from
      map_natCast (algebraMap (𝓞 (QNeg n)) (QNeg n)) _]
    ext
    · rw [QuadraticAlgebra.re_natCast, hmq]; rfl
    · rw [QuadraticAlgebra.im_natCast]; rfl
  ext x
  simp only [Shimura.idealMeetOrder, Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_span_pair,
    Shimura.mem_O4_iff']
  constructor
  · rintro ⟨⟨c, z, hz⟩, y, hy, rfl⟩
    obtain ⟨a, b, hab⟩ := hy
    simp only [smul_eq_mul] at hab
    obtain ⟨a1, a2, ha1, ha2⟩ := Shimura.int_coords hn4 hsq a
    obtain ⟨b1, b2, hb1, hb2⟩ := Shimura.int_coords hn4 hsq b
    obtain ⟨p, q, hp, hq⟩ := Shimura.int_coords hn4 hsq z
    have hy' : (y : QNeg n) = (a : QNeg n) * hW0 n + (b : QNeg n) * (QuadraticAlgebra.omega - 1) := by
      rw [← hab]; push_cast [hcm, coe_sqrtNeg]; rfl
    have him := congrArg QuadraticAlgebra.im hz
    rw [hy'] at him
    simp [ha1, ha2, hb1, hb2, hp, hq] at him
    refine ⟨a1 + a2 - 2 * b2, q, ?_⟩
    rw [hy']
    ext
    · simp [ha1, ha2, hb1, hb2]
      linear_combination him
    · simp [ha1, ha2, hb1, hb2]
      linear_combination -him
  · rintro ⟨P, Q, rfl⟩
    refine ⟨⟨P * m - 4 * Q, (Q : 𝓞 (QNeg n)) * sqrtNeg n, ?_⟩,
      (P : 𝓞 (QNeg n)) * (m : 𝓞 (QNeg n)) + ((4 * Q : ℤ) : 𝓞 (QNeg n)) * (sqrtNeg n - 1), ?_, ?_⟩
    · ext
      · simp [hmq, coe_sqrtNeg]
        ring
      · simp [hmq, coe_sqrtNeg]
        ring
    · exact ⟨_, _, rfl⟩
    · ext
      · simp [hmq, coe_sqrtNeg, map_ofNat]
        ring
      · simp [hmq, coe_sqrtNeg, map_ofNat]
        ring

/-- **`Q'' = [32(n+4), 8(n+2), (n+1)/2]`**, a Heegner form of level 32 and discriminant `−64n`, with
`τ_{Q''} = W(τ_Q + 1/4)`. -/
def tyzFormW (n : ℕ) (hn : n % 8 = 5) : HeegnerForm 32 (-64 * n) where
  A := 32 * (n + 4)
  B := 8 * (n + 2)
  C := (((n + 1) / 2 : ℕ) : ℤ)
  A_pos := by positivity
  N_dvd := ⟨n + 4, by push_cast; ring⟩
  disc := by
    have h2 : (((n + 1) / 2 : ℕ) : ℤ) * 2 = n + 1 := by omega
    linear_combination (-64 * ((n : ℤ) + 4)) * h2
  D_neg := by
    have : (0 : ℤ) < n := by omega
    linarith
  primitive := by
    set g := Int.gcd (Int.gcd (32 * ((n : ℤ) + 4)) (8 * ((n : ℤ) + 2))) (((n + 1) / 2 : ℕ) : ℤ)
    have hB : (g : ℤ) ∣ 8 * ((n : ℤ) + 2) := (Int.gcd_dvd_left ..).trans (Int.gcd_dvd_right ..)
    have hC : (g : ℤ) ∣ (((n + 1) / 2 : ℕ) : ℤ) := Int.gcd_dvd_right ..
    have hCk : (((n + 1) / 2 : ℕ) : ℤ) = 4 * ((n / 8 : ℕ) : ℤ) + 3 := by omega
    have hnk : (n : ℤ) = 8 * ((n / 8 : ℕ) : ℤ) + 5 := by omega
    rw [hCk] at hC
    rw [hnk] at hB
    have h1 : (g : ℤ) ∣ 1 := by
      have e : (1 : ℤ) = (4 * ((n / 8 : ℕ) : ℤ) + 3) * (4 * ((n / 8 : ℕ) : ℤ) + 3 +
          16 * (2 * ((n / 8 : ℕ) : ℤ) + 1) * ((n / 8 : ℕ) + 1)) -
          (2 * ((n / 8 : ℕ) : ℤ) + 1) * ((n / 8 : ℕ) + 1) * (8 * (8 * ((n / 8 : ℕ) : ℤ) + 5 + 2)) := by
        ring
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_left hC _) (dvd_mul_of_dvd_right hB _)
    exact Nat.dvd_one.mp (by exact_mod_cast h1)

/-- `τ_{Q''} = (−(n+2) + √−n)/(8(n+4))`. -/
def tauW (n : ℕ) : QNeg n := ⟨-((n : ℚ) + 2) / (8 * (n + 4)), 1 / (8 * (n + 4))⟩
/-- The homothety factor `c = (−1 + ((n+3)/2)√−n)/(n+4)`. -/
def cW (n : ℕ) : QNeg n := ⟨-1 / ((n : ℚ) + 4), ((n : ℚ) + 3) / 2 / (n + 4)⟩

theorem tyzFormW_tau (n : ℕ) (hn : n % 8 = 5) : (tyzFormW n hn).tau = Shimura.kappa n (tauW n) := by
  have h4 : ((n : ℂ) + 4) ≠ 0 := by exact_mod_cast (show n + 4 ≠ 0 by omega)
  simp only [HeegnerForm.tau, cmPoint, tyzFormW, Shimura.kappa, tauW, Shimura.sqrt_64n]
  push_cast
  field_simp
  ring

theorem tauW_mul (n : ℕ) [NeZero n] : tauW n * (32 * Shimura.tauK n + 8) = -1 := by
  have h1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have h4 : ((n : ℚ) + 4) ≠ 0 := by positivity
  ext <;> simp [tauW, Shimura.tauK, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;>
    field_simp <;> ring

omit [NeZero n] in
@[simp] theorem tauW_re : (tauW n).re = -((n : ℚ) + 2) / (8 * (n + 4)) := rfl
omit [NeZero n] in
@[simp] theorem tauW_im : (tauW n).im = 1 / (8 * ((n : ℚ) + 4)) := rfl
omit [NeZero n] in
@[simp] theorem cW_re : (cW n).re = -1 / ((n : ℚ) + 4) := rfl
omit [NeZero n] in
@[simp] theorem cW_im : (cW n).im = ((n : ℚ) + 3) / 2 / (n + 4) := rfl
omit [NeZero n] in
@[simp] theorem tauK_re : (Shimura.tauK n).re = 1 / (4 * ((n : ℚ) + 1)) := rfl
omit [NeZero n] in
@[simp] theorem tauK_im : (Shimura.tauK n).im = 1 / (4 * ((n : ℚ) + 1)) := rfl

theorem latKW (k : ℕ) (hk : n = 8 * k + 5) :
    Submodule.span ℤ ({hW0 n, hW1 n} : Set (QNeg n)) * Submodule.span ℤ {1, tauW n} =
      Submodule.span ℤ {cW n * 1, cW n * Shimura.tauK n} := by
  subst hk
  have h1 : (8 * (k : ℚ) + 5 + 1) ≠ 0 := by positivity
  have h4 : (8 * (k : ℚ) + 5 + 4) ≠ 0 := by positivity
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact Shimura.mem_span_pair_of 1 (-32 - 32 * k) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of 0 (3 + 4 * k) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of 8 32 (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of (-1) 0 (by ext <;> simp <;> field_simp <;> ring)
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact Shimura.mem_span_mul_four (hW0 _) (hW1 _) 1 (tauW _) (by simp) (by simp) (by simp)
        (by simp) 0 0 0 (-1) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_mul_four (hW0 _) (hW1 _) 1 (tauW _) (by simp) (by simp) (by simp)
        (by simp) 0 (11 - 484 * k + 21296 * (k * k)) (-(1 - 44 * k + 1936 * (k * k) + 2662 * (k * k * k)))
        (8 * (-(1 - 44 * k + 1936 * (k * k) + 2662 * (k * k * k))))
        (by ext <;> simp <;> field_simp <;> ring)

theorem latNKW (k : ℕ) (hk : n = 8 * k + 5) :
    Submodule.span ℤ ({hW0 n, hW1 n} : Set (QNeg n)) * Submodule.span ℤ {Shimura.oneN n, tauW n} =
      Submodule.span ℤ {cW n * Shimura.oneN n, cW n * Shimura.tauK n} := by
  subst hk
  have h1 : (8 * (k : ℚ) + 5 + 1) ≠ 0 := by positivity
  have h4 : (8 * (k : ℚ) + 5 + 4) ≠ 0 := by positivity
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact Shimura.mem_span_pair_of 1 (-1 - k) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of 0 (3 + 4 * k) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of 8 1 (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of (-32) 0 (by ext <;> simp <;> field_simp <;> ring)
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact Shimura.mem_span_mul_four (hW0 _) (hW1 _) (Shimura.oneN _) (tauW _) (by simp) (by simp)
        (by simp) (by simp) 1 (3 * (k + 1)) (-4 * (k + 1) * (3 * k + 2)) (-(k + 1) * (3 * k + 2))
        (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_mul_four (hW0 _) (hW1 _) (Shimura.oneN _) (tauW _) (by simp) (by simp)
        (by simp) (by simp) 0 3 (-12 * k - 8) (-3 * k - 2)
        (by ext <;> simp <;> field_simp <;> ring)

-- BEGIN copy of L321 quarter lemmas (dev only)
theorem etaD_add_quarter {d m : ℕ} (h : d = 4 * m) (z : ℂ) :
    X0.etaD d (z + 1 / 4) = cexp (2 * Real.pi * I / 24) ^ m * X0.etaD d z := by
  unfold X0.etaD
  rw [show (d : ℂ) * (z + 1 / 4) = d * z + (m : ℕ) by rw [h]; push_cast; ring, X0.eta_add_nat,
    ← Complex.exp_nat_mul]
  congr 2
  ring

theorem cexp_pi_div_two : cexp (Real.pi / 2 * I) = I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem cexp_pow_6 : cexp (2 * Real.pi * I / 24) ^ 6 = I := by
  rw [← Complex.exp_nat_mul,
    show ((6 : ℕ) : ℂ) * (2 * Real.pi * I / 24) = Real.pi / 2 * I by push_cast; ring]
  exact cexp_pi_div_two

/-- **`y(z + 1/4) = i·y(z)`** (`y` is an eta quotient in `η(4z), η(8z), η(16z), η(32z)`). -/
theorem yC_add_quarter (z : ℂ) : X0.yC (z + 1 / 4) = I * X0.yC z := by
  unfold X0.yC
  rw [etaD_add_quarter (m := 2) (by norm_num), etaD_add_quarter (m := 4) (by norm_num),
    etaD_add_quarter (m := 1) (by norm_num), etaD_add_quarter (m := 8) (by norm_num)]
  set c := cexp (2 * Real.pi * I / 24)
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have key : c ^ 16 = I * c ^ 34 := by
    rw [← cexp_pow_6, show c ^ 34 = c ^ 10 * c ^ 24 by ring, X0.cexp_pow_24]; ring
  have e : (c ^ 2 * X0.etaD 8 z) ^ 4 * (c ^ 4 * X0.etaD 16 z) ^ 2 /
      ((c ^ 1 * X0.etaD 4 z) ^ 2 * (c ^ 8 * X0.etaD 32 z) ^ 4) =
      c ^ 16 * (X0.etaD 8 z ^ 4 * X0.etaD 16 z ^ 2) /
        (c ^ 34 * (X0.etaD 4 z ^ 2 * X0.etaD 32 z ^ 4)) := by ring
  rw [e, key, show I * c ^ 34 * (X0.etaD 8 z ^ 4 * X0.etaD 16 z ^ 2) =
    c ^ 34 * (I * (X0.etaD 8 z ^ 4 * X0.etaD 16 z ^ 2)) by ring,
    mul_div_mul_left _ _ (pow_ne_zero _ hc)]
  ring

/-- `τ ↦ τ + 1/4` on `ℍ`. -/
def quarterH (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(τ : ℂ) + 1 / 4, by
    show 0 < ((τ : ℂ) + 1 / 4).im
    simpa using τ.im_pos⟩

theorem Qt_add_quarter (z : ℂ) : Shimura.Qt (z + 1 / 4) = Shimura.Qt z * I := by
  rw [Shimura.Qt_def, Shimura.Qt_def,
    show 2 * Real.pi * I * (z + 1 / 4) = 2 * Real.pi * I * z + Real.pi / 2 * I by ring,
    Complex.exp_add, cexp_pi_div_two]

/-- **`x(τ + 1/4) = −x(τ)`** (`x = 2θ(0;16τ)/(q²θ(8τ;16τ))`, tyz-cm's `xC_theta`). -/
theorem xC_add_quarter (τ : UpperHalfPlane) : X0.xC ((τ : ℂ) + 1 / 4) = -X0.xC τ := by
  have h1 := Shimura.xC_theta (quarterH τ)
  have h2 := Shimura.xC_theta τ
  change X0.xC ((quarterH τ : UpperHalfPlane) : ℂ) = _
  rw [h1, h2]
  have e1 : (16 : ℂ) * ((quarterH τ : UpperHalfPlane) : ℂ) = 16 * τ + 2 + 2 := by
    show (16 : ℂ) * ((τ : ℂ) + 1 / 4) = _; ring
  have e2 : (8 : ℂ) * ((quarterH τ : UpperHalfPlane) : ℂ) = 8 * τ + 1 + 1 := by
    show (8 : ℂ) * ((τ : ℂ) + 1 / 4) = _; ring
  have e3 : Shimura.Qt ((quarterH τ : UpperHalfPlane) : ℂ) = Shimura.Qt τ * I :=
    Qt_add_quarter τ
  rw [e1, e2, e3]
  simp only [jacobiTheta₂_add_right, jacobiTheta₂_add_left]
  rw [mul_pow, I_sq]
  ring

theorem curveAC_a₂ : X0.curveAC.a₂ = 0 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
theorem curveAC_a₄ : X0.curveAC.a₄ = 4 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
theorem curveAC_a₆ : X0.curveAC.a₆ = 0 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]

theorem nonsingular_iC {x y : ℂ} (h : X0.curveAC.toAffine.Nonsingular x y) :
    X0.curveAC.toAffine.Nonsingular (-x) (I * y) := by
  rw [nonsingular_iff', equation_iff'] at h ⊢
  simp only [Shimura.curveAC_a₁, curveAC_a₂, Shimura.curveAC_a₃, curveAC_a₄, curveAC_a₆] at h ⊢
  obtain ⟨he, hn⟩ := h
  refine ⟨by linear_combination y ^ 2 * I_sq - he, ?_⟩
  rcases hn with h | h
  · left
    intro h'
    apply h
    linear_combination h'
  · right
    intro h'
    apply h
    have : I * (2 * y) = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 I_ne_zero
    · linear_combination h0

theorem nonsingular_iC_iff {x y : ℂ} :
    X0.curveAC.toAffine.Nonsingular (-x) (I * y) ↔ X0.curveAC.toAffine.Nonsingular x y := by
  refine ⟨fun h => ?_, nonsingular_iC⟩
  have h2 := nonsingular_iC h
  have e1 : -(-x) = x := neg_neg x
  have e2 : I * (I * y) = X0.curveAC.toAffine.negY x y := by
    rw [Shimura.negY_AC, ← mul_assoc, I_mul_I]; ring
  rw [e1, e2] at h2
  exact (nonsingular_neg ..).1 h2

/-- **`φ(τ + 1/4) = [i]φ(τ)`**, on algebraic points. -/
theorem toC_iPt_of_quarter (τ τ' : UpperHalfPlane) (h : (τ' : ℂ) = τ + 1 / 4) (P : PtA)
    (hP : toC P = X0.phiC τ) : toC (iPt P) = X0.phiC τ' := by
  have hx : X0.xC τ' = -X0.xC τ := by rw [h, xC_add_quarter]
  have hy : X0.yC τ' = I * X0.yC τ := by rw [h, yC_add_quarter]
  unfold X0.phiC at hP ⊢
  by_cases hns : X0.curveAC.toAffine.Nonsingular (X0.xC τ) (X0.yC τ)
  · have hns' : X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [hx, hy]; exact nonsingular_iC hns
    rw [dif_pos hns] at hP
    rw [dif_pos hns']
    rcases P with _ | ⟨x, y, hxy⟩
    · exact absurd hP (fun h => by cases h)
    · simp only [toC, Point.map_some, Point.some.injEq] at hP
      rw [iPt_some]
      simp only [toC, Point.map_some, Point.some.injEq]
      refine ⟨?_, ?_⟩
      · rw [hx, ← hP.1]; simp
      · rw [hy, ← hP.2, map_mul]
        congr 1
        exact ιC_iQ
  · have hns' : ¬ X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [hx, hy]; exact fun h' => hns (nonsingular_iC_iff.1 h')
    rw [dif_neg hns] at hP
    rw [dif_neg hns']
    rcases P with _ | ⟨x, y, hxy⟩
    · rfl
    · exact absurd hP (fun h => by cases h)

theorem iPt_sub (P R : PtA) : iPt (P - R) = iPt P - iPt R := map_sub iHom P R

-- END copy

theorem toC_ptT' : toC Package.ptT = X0.ptTC := by
  simp [toC, Package.ptT, X0.ptTC, WeierstrassCurve.Affine.Point.map, map_ofNat]

theorem idealLat_varpi (hn : n % 8 = 5) (hsq : Squarefree n) :
    Shimura.idealLat n 4 (varpiIdeal n) = (Submodule.span ℤ {hW0 n, hW1 n}).map (Shimura.kappaLin n) := by
  rw [Shimura.idealLat, idealMeetOrder_varpi hn hsq,
    show Shimura.kappa n = Shimura.kappaLin n from funext fun x => (Shimura.kappaLin_apply n x).symm,
    Submodule.span_image, Submodule.span_eq]

theorem idealLat_varpi_mul (hn : n % 8 = 5) (hsq : Squarefree n) :
    Shimura.idealLat n 4 (varpiIdeal n) * (tyzFormW n hn).lat =
      (tyzForm n hn).lat.map (LinearMap.mulLeft ℤ (Shimura.kappa n (cW n))) := by
  rw [idealLat_varpi hn hsq, Shimura.lat_eq_map _ n _ (tyzFormW_tau n hn),
    Shimura.lat_eq_map _ n _ (Shimura.tyzForm_tau n hn), Shimura.map_mulLeft_span_pair,
    Shimura.kappaLin, ← Submodule.map_mul, latKW (n / 8) (by omega)]

theorem idealLat_varpi_mulN (hn : n % 8 = 5) (hsq : Squarefree n) :
    Shimura.idealLat n 4 (varpiIdeal n) * (tyzFormW n hn).latN =
      (tyzForm n hn).latN.map (LinearMap.mulLeft ℤ (Shimura.kappa n (cW n))) := by
  rw [idealLat_varpi hn hsq, Shimura.latN_eq_map _ n _ (tyzFormW_tau n hn),
    Shimura.latN_eq_map _ n _ (Shimura.tyzForm_tau n hn), Shimura.map_mulLeft_span_pair,
    Shimura.kappaLin, ← Submodule.map_mul, latNKW (n / 8) (by omega)]

/-- `τ_{Q''} = W(τ_Q + 1/4)`. -/
theorem tyzFormW_tauH (hn : n % 8 = 5) :
    ((tyzFormW n hn).tauH : ℂ) =
      ((Shimura.frickeH (quarterH (tyzForm n hn).tauH) : UpperHalfPlane) : ℂ) := by
  have hτ : ((tyzForm n hn).tauH : ℂ) = Shimura.kappaAlg n (Shimura.tauK n) := by
    rw [Shimura.kappaAlg_apply, ← Shimura.tyzForm_tau n hn]; rfl
  have hτ' : ((tyzFormW n hn).tauH : ℂ) = Shimura.kappaAlg n (tauW n) := by
    rw [Shimura.kappaAlg_apply, ← tyzFormW_tau n hn]; rfl
  have hrel := congrArg (Shimura.kappaAlg n) (tauW_mul n)
  simp only [map_mul, map_add, map_neg, map_one, map_ofNat] at hrel
  rw [← hτ, ← hτ'] at hrel
  set τ := ((tyzForm n hn).tauH : ℂ)
  have hne : (32 * (τ + 1 / 4)) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact (tyzForm n hn).tauH.im_pos.ne' this
  show _ = -1 / (32 * (τ + 1 / 4))
  rw [eq_div_iff hne]
  linear_combination hrel

/-- **`f₀(P_{Q''}) = T − [i]f₀(P_n)`** (given algebraicity of the Heegner point). -/
theorem heegnerPt_tyzFormW (hA : CMAlgebraic) (hn : n % 8 = 5) :
    heegnerPt (tyzFormW n hn) = ptT - iPt (heegnerPt (tyzForm n hn)) := by
  set Q := tyzForm n hn
  obtain ⟨P, hP⟩ := hA _ Q
  rw [heegnerPt_eq Q hP]
  apply heegnerPt_eq
  set τ₁ := quarterH Q.tauH
  set τ₂ := Shimura.frickeH τ₁
  have hτ₂ : (tyzFormW n hn).tauH = τ₂ := UpperHalfPlane.ext (tyzFormW_tauH hn)
  have e2 : X0.phiC τ₂ + X0.phiC τ₁ = X0.ptTC := Shimura.etaModelFricke τ₁ τ₂ rfl
  have h1 : toC (iPt P) = X0.phiC τ₁ := toC_iPt_of_quarter Q.tauH τ₁ rfl _ hP
  rw [hτ₂, map_sub, toC_ptT', h1, ← e2]
  abel

theorem acts4_inv {ρ : GalQ} {c : Pic (O4 n)} (hρ : ActsAsArtin4 ρ n c) :
    ActsAsArtin4 ρ⁻¹ n c⁻¹ := by
  intro x
  have e : artin4 n c (artin4 n c⁻¹ x) = x := by
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have h := hρ (artin4 n c⁻¹ x)
  rw [e] at h
  calc ρ⁻¹ (embed n (x : SeparableClosure (QNeg n)))
      = ρ⁻¹ (ρ (embed n ((artin4 n c⁻¹ x : H4 n) : SeparableClosure (QNeg n)))) := by rw [h]
    _ = _ := ρ.symm_apply_apply _

set_option maxRecDepth 10000 in
/-- `ρ` acting on `H_{n,4}` as `c` (through `embed n`) acts as `c` through an embedding normalized by
`ιC(e(√−n)) = i√n`, either directly or after inverting `ρ`. -/
theorem normalized_cases {c : Pic (O4 n)} {ρ : GalQ} (hρ : ActsAsArtin4 ρ n c) :
    ∃ e : SeparableClosure (QNeg n) →ₐ[ℚ] Qbar,
      ιC (e (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt n : ℂ) ∧
      ((∀ x : ringClassField (conductorOrder (QNeg n) 4),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg n) 4) c x)) ∨
      (∀ x : ringClassField (conductorOrder (QNeg n) 4),
        ρ⁻¹ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg n) 4) c x))) := by
  set r := embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)
  have hr : r ^ 2 = -(n : Qbar) := by
    simp only [r, ← map_pow, Shimura.omega_sq', map_neg, map_natCast]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hC : ιC r ^ 2 = (I * (Real.sqrt n : ℂ)) ^ 2 := by
    rw [← map_pow, hr, mul_pow, I_sq, sq, Shimura.sqrt_mul_self_C]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hC with h | h
  · exact ⟨embed n, h, Or.inl hρ⟩
  · obtain ⟨γ, hγ⟩ := Shimura.exists_galQ_neg hn0 hr
    have hr0 : r ≠ 0 := by
      intro h0; rw [h0] at hr
      have : (n : Qbar) = 0 := by linear_combination hr
      exact NeZero.ne n (by exact_mod_cast this)
    have hγinv : γ⁻¹ r = -r := by
      apply γ.injective
      show γ (γ.symm r) = γ (-r)
      rw [AlgEquiv.apply_symm_apply, map_neg, hγ, neg_neg]
    have hne : γ⁻¹ r ≠ r := by
      rw [hγinv]; intro h'
      apply hr0
      have : (2 : Qbar) * r = 0 := by linear_combination -h'
      simpa using this
    have hconj := RingClassBridge.actsAsArtin4_conj (γ := γ⁻¹) hne (acts4_inv hρ)
    rw [inv_inv, inv_inv] at hconj
    refine ⟨γ.toAlgHom.comp (embed n), ?_, Or.inr fun x => ?_⟩
    · show ιC (γ r) = _
      rw [hγ, map_neg, h, neg_neg]
    · have h1 := hconj x
      simp only [AlgEquiv.mul_apply] at h1
      show ρ⁻¹ (γ (embed n (x : SeparableClosure (QNeg n)))) = γ (embed n _)
      rw [← h1]; exact (γ.apply_symm_apply _).symm

end ZInQ.Contrib.TYZGenus.T321W
