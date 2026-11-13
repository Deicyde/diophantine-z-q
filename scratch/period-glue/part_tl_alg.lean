/-! ## period-glue: quaternion and matrix algebra for `QMTwistLattice` (Mathlib + `QMLattice`)

Task period-glue, 2026-11-13. Over N5's `B = (2, −3)` and its real embedding `ι`
(`BPAnalytic.QM.iota`): `ι` is multiplicative; an explicit intertwiner `u ≠ 0` with `i u = u p`,
`j u = u q` for any pair `p² = 2`, `q² = −3`, `pq = −qp` (the trace of `w ↦ u(w)` is `−24`; this is
Skolem–Noether for `B`, made explicit); the commutant of `ι(i), ι(j)` in `M₂(ℂ)` is the scalars; a
real matrix killing a non-real vector `(τ, 1)` is zero. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlueTL

open BPAnalytic.QM Matrix

/-- `ι(x)` as a complex matrix. -/
def Mc (x : B) : Matrix (Fin 2) (Fin 2) ℂ := (iota x).map (fun r : ℝ => (r : ℂ))

theorem iota_explicit (x : B) : iota x =
    !![(x.re : ℝ) + √2 * x.imI, -3 * x.imJ - 3 * √2 * x.imK; (x.imJ : ℝ) - √2 * x.imK,
      (x.re : ℝ) - √2 * x.imI] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [iota, Mi, Mj] <;> ring

theorem iota_mul' (x y : B) : iota (x * y) = iota x * iota y := by
  rw [iota_explicit, iota_explicit, iota_explicit]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast <;> ring_nf <;>
    (try simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) <;> (try ring_nf)

theorem iota_add' (x y : B) : iota (x + y) = iota x + iota y := by
  rw [iota_explicit, iota_explicit, iota_explicit]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> push_cast <;> ring

theorem iota_one' : iota 1 = 1 := by
  rw [iota_explicit]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem iota_ratCast (r : ℚ) : iota (r : B) = (r : ℝ) • 1 := by
  rw [iota_explicit]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem Mc_mul (x y : B) : Mc (x * y) = Mc x * Mc y := by
  show (iota (x * y)).map Complex.ofRealHom = (iota x).map Complex.ofRealHom * (iota y).map Complex.ofRealHom
  rw [iota_mul', Matrix.map_mul]

theorem Mc_add (x y : B) : Mc (x + y) = Mc x + Mc y := by
  ext i j; simp [Mc, iota_add']

theorem Mc_ratCast (r : ℚ) : Mc (r : B) = ((r : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [Mc, iota_ratCast]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem Mc_explicit (x : B) : Mc x =
    !![((x.re : ℝ) : ℂ) + (√2 : ℂ) * ((x.imI : ℝ) : ℂ),
      -3 * ((x.imJ : ℝ) : ℂ) - 3 * (√2 : ℂ) * ((x.imK : ℝ) : ℂ);
      ((x.imJ : ℝ) : ℂ) - (√2 : ℂ) * ((x.imK : ℝ) : ℂ), ((x.re : ℝ) : ℂ) - (√2 : ℂ) * ((x.imI : ℝ) : ℂ)] := by
  simp only [Mc, iota_explicit]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-! ### The intertwiner (Skolem–Noether for `B`, explicit) -/

theorem intertwine1 {R : Type*} [Ring R] (i p w c : R) (hc : ∀ x, c * x = x * c)
    (hi : i * i = c) (hp : p * p = c) :
    i * (c * w + i * w * p) = (c * w + i * w * p) * p := by
  have e1 : i * (c * w + i * w * p) = c * (i * w) + c * w * p := by
    rw [mul_add, ← mul_assoc, ← hc i, mul_assoc, ← mul_assoc i (i * w) p, ← mul_assoc i i w, hi]
  have e2 : (c * w + i * w * p) * p = c * w * p + c * (i * w) := by
    rw [add_mul, mul_assoc (i * w) p p, hp, ← hc]
  rw [e1, e2, add_comm]

theorem intertwine2 {R : Type*} [Ring R] (i j p q u c : R) (hc : ∀ x, c * x = x * c)
    (hij : i * j = -(j * i)) (hpq : p * q = -(q * p)) (hu : i * u = u * p) :
    i * (c * u + j * u * q) = (c * u + j * u * q) * p := by
  have e1 : i * (c * u + j * u * q) = c * (u * p) - j * (u * p) * q := by
    rw [mul_add, ← mul_assoc, ← hc i, mul_assoc, hu, ← mul_assoc i (j * u) q, ← mul_assoc i j u,
      hij, neg_mul, neg_mul, mul_assoc j i u, hu, sub_eq_add_neg]
  have e2 : (c * u + j * u * q) * p = c * (u * p) - j * (u * p) * q := by
    have hqp : q * p = -(p * q) := by rw [hpq, neg_neg]
    rw [add_mul, mul_assoc c u p, mul_assoc (j * u) q p, hqp, mul_neg, sub_eq_add_neg,
      ← mul_assoc (j * u) p q, mul_assoc j u p]
  rw [e1, e2]

/-- `i`, `j`, `k = ij` of `B`. -/
def iB : B := ⟨0, 1, 0, 0⟩
def jB : B := ⟨0, 0, 1, 0⟩
def kB : B := ⟨0, 0, 0, 1⟩

theorem iB_sq : iB * iB = 2 := by
  ext <;> simp [iB, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat,
    QuaternionAlgebra.imK_ofNat]
theorem jB_sq : jB * jB = -3 := by
  ext <;> simp [jB, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat,
    QuaternionAlgebra.imK_ofNat] <;> norm_num
theorem iB_jB : iB * jB = -(jB * iB) := by ext <;> simp [iB, jB]

/-- The intertwiner built from `w`. -/
def U (p q w : B) : B := (-3) * (2 * w + iB * w * p) + jB * (2 * w + iB * w * p) * q

theorem U_spec (p q w : B) (hp : p * p = 2) (hq : q * q = -3) (hpq : p * q = -(q * p)) :
    iB * U p q w = U p q w * p ∧ jB * U p q w = U p q w * q := by
  have hc2 : ∀ x : B, (2 : B) * x = x * 2 := fun x => (Commute.ofNat_left 2 x).eq
  have hc3 : ∀ x : B, (-3 : B) * x = x * (-3) := fun x => (Commute.ofNat_left 3 x).neg_left.eq
  have h1 := intertwine1 iB p w 2 hc2 iB_sq hp
  exact ⟨intertwine2 iB jB p q _ (-3) hc3 iB_jB hpq h1, intertwine1 jB q _ (-3) hc3 jB_sq hq⟩

/-- **An intertwiner exists (proved).** -/
theorem exists_intertwiner (p q : B) (hp : p * p = 2) (hq : q * q = -3)
    (hpq : p * q = -(q * p)) : ∃ u : B, u ≠ 0 ∧ iB * u = u * p ∧ jB * u = u * q := by
  by_contra hne
  push Not at hne
  have h0 : ∀ w, U p q w = 0 := fun w => by
    by_contra h
    obtain ⟨h1, h2⟩ := U_spec p q w hp hq hpq
    exact hne _ h h1 h2
  have e1 := congrArg QuaternionAlgebra.re (h0 1)
  have e2 := congrArg QuaternionAlgebra.imI (h0 iB)
  have e3 := congrArg QuaternionAlgebra.imJ (h0 jB)
  have e4 := congrArg QuaternionAlgebra.imK (h0 kB)
  simp [U, iB, jB, kB, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] at e1 e2 e3 e4
  linarith

/-! ### Matrices -/

/-- **The commutant of `ι(i)`, `ι(j)` in `M₂(ℂ)` is the scalars (proved).** -/
theorem commutant_scalar (S : Matrix (Fin 2) (Fin 2) ℂ) (hi : S * Mc iB = Mc iB * S)
    (hj : S * Mc jB = Mc jB * S) : S = S 0 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hs : (√2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr two_pos)
  have a01 := congrFun (congrFun hi 0) 1
  have a10 := congrFun (congrFun hi 1) 0
  have b01 := congrFun (congrFun hj 0) 1
  simp [Mc_explicit, iB, jB, Matrix.mul_apply, Fin.sum_univ_two] at a01 a10 b01
  have s01 : S 0 1 = 0 := by
    have : (2 * (√2 : ℂ)) * S 0 1 = 0 := by linear_combination -a01
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hs)
  have s10 : S 1 0 = 0 := by
    have : (2 * (√2 : ℂ)) * S 1 0 = 0 := by linear_combination a10
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hs)
  have s11 : S 1 1 = S 0 0 := by linear_combination -b01 / 3
  ext i j; fin_cases i <;> fin_cases j <;> simp [s01, s10, s11]

/-- **A real matrix `ι(x)` killing a non-real vector `(τ, 1)` is zero (proved).** -/
theorem eq_zero_of_mulVec (x : B) (τ : ℂ) (hτ : τ.im ≠ 0) (h : Mc x *ᵥ ![τ, 1] = 0) : x = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Mc_explicit, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have r0 := congrArg Complex.re h0
  have i0 := congrArg Complex.im h0
  have r1 := congrArg Complex.re h1
  have i1 := congrArg Complex.im h1
  simp at r0 i0 r1 i1
  have hs : (√2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
  have A : (x.re : ℝ) + √2 * x.imI = 0 := i0.resolve_right hτ
  have C : (x.imJ : ℝ) - √2 * x.imK = 0 := i1.resolve_right hτ
  have Bq : -3 * (x.imJ : ℝ) - 3 * √2 * x.imK = 0 := by linear_combination r0 - τ.re * A
  have D : (x.re : ℝ) - √2 * x.imI = 0 := by linear_combination r1 - τ.re * C
  have hre : (x.re : ℝ) = 0 := by linear_combination (A + D) / 2
  have himI : (x.imI : ℝ) = 0 := by
    have : √2 * (x.imI : ℝ) = 0 := by linear_combination (A - D) / 2
    exact (mul_eq_zero.mp this).resolve_left hs
  have himK : (x.imK : ℝ) = 0 := by
    have : √2 * (x.imK : ℝ) = 0 := by linear_combination -(Bq + 3 * C) / 6
    exact (mul_eq_zero.mp this).resolve_left hs
  have himJ : (x.imJ : ℝ) = 0 := by linear_combination C + √2 * himK
  have e1 : x.re = 0 := by exact_mod_cast hre
  have e2 : x.imI = 0 := by exact_mod_cast himI
  have e3 : x.imJ = 0 := by exact_mod_cast himJ
  have e4 : x.imK = 0 := by exact_mod_cast himK
  ext <;> simp [e1, e2, e3, e4]

/-! ### The lattice `Λ_τ` and Möbius transformations -/

/-- N5's coordinates `n ↦ n₀ + n₁ i + n₂ (1+j)/2 + n₃ (i+ij)/2` (as `LeafQM.ofInt`). -/
def ofIntB (n : Fin 4 → ℤ) : B :=
  ⟨n 0 + (n 2 : ℚ) / 2, n 1 + (n 3 : ℚ) / 2, (n 2 : ℚ) / 2, (n 3 : ℚ) / 2⟩

theorem Mc_ofIntB_mulVec (n : Fin 4 → ℤ) (w : Fin 2 → ℂ) :
    Mc (ofIntB n) *ᵥ w = ∑ k, n k • (Mc (oBasis k) *ᵥ w) := by
  ext i; fin_cases i <;>
    simp [Mc_explicit, ofIntB, oBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Fin.sum_univ_two] <;> ring

/-- **Points of `Λ_τ` (proved).** `Λ_τ = {ι(a)(τ, 1)ᵀ : a ∈ 𝒪}`. -/
theorem mem_qmLattice_iff {τ : ℂ} (hτ : τ.im ≠ 0) (z : Fin 2 → ℂ) :
    z ∈ qmLattice hτ ↔ ∃ n : Fin 4 → ℤ, z = Mc (ofIntB n) *ᵥ ![τ, 1] := by
  rw [qmLattice_eq, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, by rw [Mc_ofIntB_mulVec]; rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by rw [Mc_ofIntB_mulVec]; rfl⟩

/-- **A real matrix carrying `(τ, 1)` to a multiple of `(τ', 1)` (`τ, τ' ∈ ℍ`) has positive
determinant and maps `τ` to `τ'` (proved).** -/
theorem mobius_of_vec (x : B) (c : ℂ) (τ τ' : UpperHalfPlane)
    (h : (![(τ' : ℂ), 1] : Fin 2 → ℂ) = c • (Mc x *ᵥ ![(τ : ℂ), 1])) :
    0 < (iota x).det ∧ ∀ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = iota x → g • τ = τ' := by
  set m := iota x with hm
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Mc, ← hm] at h0 h1
  set N : ℂ := (m 0 0 : ℂ) * τ + m 0 1 with hN
  set D : ℂ := (m 1 0 : ℂ) * τ + m 1 1 with hD
  have hDN : (τ' : ℂ) * D = N := by linear_combination D * h0 - N * h1
  have hD0 : D ≠ 0 := by
    intro h0'; rw [h0', mul_zero] at h1; exact one_ne_zero h1
  have hre := congrArg Complex.re hDN
  have him := congrArg Complex.im hDN
  simp [hN, hD] at hre him
  have hy := τ.im_pos
  have hy' := τ'.im_pos
  have hS : 0 < (m 1 0 * τ.re + m 1 1) ^ 2 + (m 1 0 * τ.im) ^ 2 := by
    rcases (add_nonneg (sq_nonneg (m 1 0 * τ.re + m 1 1)) (sq_nonneg (m 1 0 * τ.im))).lt_or_eq with h' | h'
    · exact h'
    · exfalso; apply hD0
      have e1 : m 1 0 * τ.im = 0 := by nlinarith [sq_nonneg (m 1 0 * τ.re + m 1 1), sq_nonneg (m 1 0 * τ.im)]
      have e0 : m 1 0 = 0 := (mul_eq_zero.mp e1).resolve_right hy.ne'
      have e2 : m 1 1 = 0 := by rw [e0] at h'; nlinarith [sq_nonneg (m 1 1)]
      rw [hD, e0, e2]; simp
  have hdet : m.det * τ.im = τ'.im * ((m 1 0 * τ.re + m 1 1) ^ 2 + (m 1 0 * τ.im) ^ 2) := by
    rw [Matrix.det_fin_two]
    linear_combination (m 1 0 * τ.im) * hre - (m 1 0 * τ.re + m 1 1) * him
  have hdetpos : 0 < m.det := by
    have : 0 < m.det * τ.im := by rw [hdet]; positivity
    exact pos_of_mul_pos_left this hy.le
  refine ⟨hdetpos, fun g hg => ?_⟩
  have hgdet : 0 < g.det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg]; exact hdetpos
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hgdet, div_eq_iff (UpperHalfPlane.denom_ne_zero g τ)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hg]
  linear_combination -hDN

end HSyn.G0Split.FibreQM.PeriodGlueTL

end
