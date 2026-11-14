import TailK

/-!
# leafq-check: `QMHauptmodul`'s CM clauses from the values at three points

Over leaf-fold4's chain (`import TailK`; `HDec.PkgI1.QMHauptmodul` is the chain's constant). The CM points
of each discriminant `−4, −3, −24` form one `Γ*`-orbit (proved here by descents as in `GammaStarGen.lean`),
so `QMHauptmodul` follows from `QMHauptmodulBase`, the same statement with each CM clause asserted only at
the fixed points of `ι(x)` for one element `x = i + j`, `(1 + j)/2`, `2j + ij` (period-map's `x4`, `x3`,
`x24`). Check: `scratch/leafq-check/chk.sh scratch/leafq-check/QMHauptmodulCM.lean`.
-/

set_option linter.all false

namespace HDec.LeafQCheck.HM

open PkgI1

theorem sqrt2_sq' : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem iota_apply (x : PkgI1.B) : PkgI1.iota x =
    !![(x.re : ℝ) + x.imI * √2, -3 * (x.imJ : ℝ) - 3 * √2 * x.imK;
       (x.imJ : ℝ) - √2 * x.imK, (x.re : ℝ) - x.imI * √2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PkgI1.iota, PkgI1.Mi, PkgI1.Mj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem iota_mul (x y : PkgI1.B) : PkgI1.iota (x * y) = PkgI1.iota x * PkgI1.iota y := by
  rw [iota_apply, iota_apply, iota_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    (try simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) <;> (try ring_nf)

/-- The reduced norm. -/
def nrd (x : PkgI1.B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

theorem det_iota_eq (x : PkgI1.B) : (PkgI1.iota x).det = (nrd x : ℝ) := by
  rw [iota_apply, Matrix.det_fin_two_of, nrd]
  push_cast
  linear_combination (-(x.imI : ℝ) ^ 2 - 3 * (x.imK : ℝ) ^ 2) * sqrt2_sq'

theorem nrd_mul (x y : PkgI1.B) : nrd (x * y) = nrd x * nrd y := by
  simp [nrd]; ring

theorem iota_ratCast (q : ℚ) : PkgI1.iota (q : PkgI1.B) = (q : ℝ) • 1 := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem inO_iff (v : PkgI1.B) : PkgI1.InO v ↔ ∃ n0 n1 n2 n3 : ℤ,
    v = ⟨n0 + n2 / 2, n1 + n3 / 2, n2 / 2, n3 / 2⟩ := by
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n 0, n 1, n 2, n 3, ?_⟩
    ext <;> simp [PkgI1.oBasis, Fin.sum_univ_four] <;> ring
  · rintro ⟨n0, n1, n2, n3, rfl⟩
    refine ⟨![n0, n1, n2, n3], ?_⟩
    ext <;> simp [PkgI1.oBasis, Fin.sum_univ_four] <;> ring

theorem inv_eq {x z : PkgI1.B} (hxz : x * z = 1) (hN : nrd x ≠ 0) :
    z = ⟨x.re / nrd x, -x.imI / nrd x, -x.imJ / nrd x, -x.imK / nrd x⟩ := by
  set w : PkgI1.B := ⟨x.re / nrd x, -x.imI / nrd x, -x.imJ / nrd x, -x.imK / nrd x⟩ with hw_def
  have hN' : x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 ≠ 0 := hN
  have hw : w * x = 1 := by
    ext <;> simp [w, nrd] <;> field_simp <;> ring
  calc z = (w * x) * z := by rw [hw, one_mul]
    _ = w * (x * z) := mul_assoc _ _ _
    _ = w := by rw [hxz, mul_one]



/-! ### The hyperboloid form -/

/-- The bilinear form of `nrd` on pure quaternions. -/
def form (v u : PkgI1.B) : ℚ := -2 * v.imI * u.imI + 3 * v.imJ * u.imJ - 6 * v.imK * u.imK

/-- Two timelike vectors in the upper cone (`imJ > 0`) pair positively (reverse Cauchy–Schwarz). -/
theorem form_pos {v u : PkgI1.B} (hv : 0 < form v v) (hu : 0 < form u u) (hv' : 0 < v.imJ)
    (hu' : 0 < u.imJ) : 0 < form v u := by
  simp only [form] at *
  set X := 2 * v.imI * u.imI + 6 * v.imK * u.imK
  have hL : X ^ 2 ≤ (2 * v.imI ^ 2 + 6 * v.imK ^ 2) * (2 * u.imI ^ 2 + 6 * u.imK ^ 2) := by
    nlinarith [sq_nonneg (v.imI * u.imK - v.imK * u.imI)]
  have hSv : 0 ≤ 2 * v.imI ^ 2 + 6 * v.imK ^ 2 := by positivity
  have hSu : 0 ≤ 2 * u.imI ^ 2 + 6 * u.imK ^ 2 := by positivity
  have hP : (2 * v.imI ^ 2 + 6 * v.imK ^ 2) * (2 * u.imI ^ 2 + 6 * u.imK ^ 2) <
      (3 * v.imJ ^ 2) * (3 * u.imJ ^ 2) := by
    apply mul_lt_mul'' <;> nlinarith
  by_contra hc
  push_neg at hc
  have hX : 3 * v.imJ * u.imJ ≤ X := by linarith
  have h0 : 0 < 3 * v.imJ * u.imJ := by positivity
  nlinarith

theorem imJ_pos_of_form {v u : PkgI1.B} (hv : 0 < form v v) (hu : 0 < form u u) (hu' : 0 < u.imJ)
    (h : 0 < form v u) : 0 < v.imJ := by
  rcases lt_trichotomy v.imJ 0 with hn | hz | hp
  · have h' := form_pos (v := -v) (by simpa [form] using hv) hu (by simpa using hn) hu'
    simp [form] at h' h
    linarith
  · simp [form, hz] at hv; nlinarith [sq_nonneg v.imI, sq_nonneg v.imK]
  · exact hp

theorem pure_of_sqN {v : PkgI1.B} (N : ℚ) (hN : 0 < N) (h : v * v = -((N : ℚ) : PkgI1.B)) :
    v.re = 0 ∧ form v v = N := by
  have h1 : v.re ^ 2 + 2 * v.imI ^ 2 - 3 * v.imJ ^ 2 + 6 * v.imK ^ 2 = -N := by
    have := congrArg QuaternionAlgebra.re h; simp at this; linear_combination this
  have h2 : v.re * v.imI = 0 := by
    have := congrArg QuaternionAlgebra.imI h; simp at this; linear_combination this / 2
  have h3 : v.re * v.imJ = 0 := by
    have := congrArg QuaternionAlgebra.imJ h; simp at this; linear_combination this / 2
  have h4 : v.re * v.imK = 0 := by
    have := congrArg QuaternionAlgebra.imK h; simp at this; linear_combination this / 2
  have key : v.re ^ 2 * (v.re ^ 2 + N) = 0 := by
    linear_combination v.re ^ 2 * h1 - 2 * (v.re * v.imI) * h2 + 3 * (v.re * v.imJ) * h3
      - 6 * (v.re * v.imK) * h4
  have hre : v.re = 0 := by
    rcases mul_eq_zero.1 key with h | h
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    · nlinarith [sq_nonneg v.re]
  refine ⟨hre, ?_⟩
  rw [hre] at h1; simp only [form]; linear_combination -h1

/-! ### The generic orbit induction -/

/-- Normalizer data: `g` and its inverse `gi` normalize `𝒪`, `nrd g > 0`. -/
def NormData (g gi : PkgI1.B) : Prop :=
  g * gi = 1 ∧ gi * g = 1 ∧ (∀ z, PkgI1.InO z → PkgI1.InO (g * z * gi) ∧ PkgI1.InO (gi * z * g)) ∧
    0 < nrd g

theorem NormData.one : NormData 1 1 :=
  ⟨mul_one 1, mul_one 1, fun z hz => by simpa using hz, by norm_num [nrd]⟩

theorem NormData.mul {g gi h hi : PkgI1.B} (hg : NormData g gi) (hh : NormData h hi) :
    NormData (g * h) (hi * gi) := by
  obtain ⟨g1, g2, g3, g4⟩ := hg
  obtain ⟨h1, h2, h3, h4⟩ := hh
  refine ⟨?_, ?_, fun z hz => ⟨?_, ?_⟩, ?_⟩
  · calc g * h * (hi * gi) = g * (h * hi) * gi := by simp only [mul_assoc]
      _ = 1 := by rw [h1, mul_one, g1]
  · calc hi * gi * (g * h) = hi * (gi * g) * h := by simp only [mul_assoc]
      _ = 1 := by rw [g2, mul_one, h2]
  · have e : g * h * z * (hi * gi) = g * (h * z * hi) * gi := by simp only [mul_assoc]
    rw [e]; exact (g3 _ (h3 z hz).1).1
  · have e : hi * gi * z * (g * h) = hi * (gi * z * g) * h := by simp only [mul_assoc]
    rw [e]; exact (h3 _ (g3 z hz).2).2
  · rw [nrd_mul]; exact mul_pos g4 h4

theorem NormData.symm {g gi : PkgI1.B} (hg : NormData g gi) : NormData gi g := by
  obtain ⟨g1, g2, g3, g4⟩ := hg
  refine ⟨g2, g1, fun z hz => ⟨(g3 z hz).2, (g3 z hz).1⟩, ?_⟩
  have h := congrArg nrd g1
  rw [nrd_mul] at h
  have : nrd (1 : PkgI1.B) = 1 := by norm_num [nrd]
  rw [this] at h
  nlinarith [mul_pos g4 g4]

theorem orbit_of_descent (E : PkgI1.B → Prop) (meas : PkgI1.B → ℚ) (b : PkgI1.B)
    (hint : ∀ w, E w → ∃ k : ℕ, meas w = k)
    (hbase : ∀ w, E w → meas w ≤ meas b → w = b)
    (hstep : ∀ w, E w → meas b < meas w → ∃ s si, NormData s si ∧ E (s * w * si) ∧
      meas (s * w * si) < meas w) :
    ∀ w, E w → ∃ g gi, NormData g gi ∧ g * b * gi = w := by
  intro w hw
  obtain ⟨k, hk⟩ := hint w hw
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    by_cases hb : meas w ≤ meas b
    · exact ⟨1, 1, NormData.one, by rw [hbase w hw hb]; simp⟩
    · push_neg at hb
      obtain ⟨s, si, hs, hE, hlt⟩ := hstep w hw hb
      obtain ⟨k', hk'⟩ := hint _ hE
      have hkk : k' < k := by rw [hk, hk'] at hlt; exact_mod_cast hlt
      obtain ⟨g, gi, hg, hgb⟩ := ih k' hkk _ hE hk'
      refine ⟨si * g, gi * s, hs.symm.mul hg, ?_⟩
      have h2 : si * s = 1 := hs.2.1
      calc si * g * b * (gi * s) = si * (g * b * gi) * s := by simp only [mul_assoc]
        _ = si * (s * w * si) * s := by rw [hgb]
        _ = (si * s) * w * (si * s) := by simp only [mul_assoc]
        _ = w := by rw [h2, one_mul, mul_one]

end HDec.LeafQCheck.HM
