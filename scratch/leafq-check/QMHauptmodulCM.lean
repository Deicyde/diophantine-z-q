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

/-! ### Elements -/

def a4 : PkgI1.B := ⟨1, 1, 1, 0⟩
def a4i : PkgI1.B := ⟨1 / 2, -1 / 2, -1 / 2, 0⟩
def a6 : PkgI1.B := ⟨-3 / 2, 0, 1 / 2, 0⟩
def a6i : PkgI1.B := ⟨-1 / 2, 0, -1 / 6, 0⟩
def mu : PkgI1.B := ⟨0, 0, 2, 1⟩
def mui : PkgI1.B := ⟨0, 0, -1 / 3, -1 / 6⟩
/-- `y = i + j` (`y² = −1`). -/
def by4 : PkgI1.B := ⟨0, 1, 1, 0⟩
/-- `j` (`j² = −3`). -/
def bj : PkgI1.B := ⟨0, 0, 1, 0⟩

theorem conj_a4 : ∀ w, PkgI1.InO w → PkgI1.InO (a4 * w * a4i) ∧ PkgI1.InO (a4i * w * a4) := by
  intro w hw
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff w).1 hw
  constructor
  · refine (inO_iff _).2 ⟨n0 + 2*n1 - n2, -n1 + n2 + n3, -4*n1 + 3*n2, -2*n1 + n2 - n3, ?_⟩
    ext <;> simp [a4, a4i] <;> ring
  · refine (inO_iff _).2 ⟨n0 + 2*n1 - n2 + 2*n3, -3*n1 + 2*n2 - 3*n3, -4*n1 + 3*n2 - 4*n3, 2*n1 - n2 + n3, ?_⟩
    ext <;> simp [a4, a4i] <;> ring

theorem conj_a6 : ∀ w, PkgI1.InO w → PkgI1.InO (a6 * w * a6i) ∧ PkgI1.InO (a6i * w * a6) := by
  intro w hw
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff w).1 hw
  constructor
  · refine (inO_iff _).2 ⟨n0, -n3, n2, n1 + n3, ?_⟩
    ext <;> simp [a6, a6i] <;> ring
  · refine (inO_iff _).2 ⟨n0, n1 + n3, n2, -n1, ?_⟩
    ext <;> simp [a6, a6i] <;> ring

theorem conj_mu : ∀ w, PkgI1.InO w → PkgI1.InO (mu * w * mui) ∧ PkgI1.InO (mui * w * mu) := by
  intro w hw
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff w).1 hw
  constructor
  · refine (inO_iff _).2 ⟨n0 - n2 + 2*n3, -n1 - n2 + n3, 3*n2 - 4*n3, 2*n2 - 3*n3, ?_⟩
    ext <;> simp [mu, mui] <;> ring
  · refine (inO_iff _).2 ⟨n0 - n2 + 2*n3, -n1 - n2 + n3, 3*n2 - 4*n3, 2*n2 - 3*n3, ?_⟩
    ext <;> simp [mu, mui] <;> ring

theorem nd_a4 : NormData a4 a4i :=
  ⟨by ext <;> simp [a4, a4i] <;> norm_num, by ext <;> simp [a4, a4i] <;> norm_num, conj_a4,
    by norm_num [nrd, a4]⟩
theorem nd_a6 : NormData a6 a6i :=
  ⟨by ext <;> simp [a6, a6i] <;> norm_num, by ext <;> simp [a6, a6i] <;> norm_num, conj_a6,
    by norm_num [nrd, a6]⟩
theorem nd_mu : NormData mu mui :=
  ⟨by ext <;> simp [mu, mui] <;> norm_num, by ext <;> simp [mu, mui] <;> norm_num, conj_mu,
    by norm_num [nrd, mu]⟩

/-! ### The orbit predicate and conjugation -/

/-- Pure elements `w ∈ 𝒪` with `w² = −N` on the upper sheet. -/
def EN (N : ℚ) (w : PkgI1.B) : Prop :=
  PkgI1.InO w ∧ w * w = -((N : ℚ) : PkgI1.B) ∧ 0 < w.imJ

theorem scal_mid (s si : PkgI1.B) (q : ℚ) : s * ((q : ℚ) : PkgI1.B) * si = ((q : ℚ) : PkgI1.B) * (s * si) := by
  ext <;> simp <;> ring

theorem EN_conj {N : ℚ} (hN : 0 < N) {s si u b w : PkgI1.B} (hs : NormData s si)
    (hu : 0 < form u u) (hu' : 0 < u.imJ) (hb : 0 < form b b) (hb' : 0 < b.imJ)
    (hf : ∀ v : PkgI1.B, v.re = 0 → form (s * v * si) b = form v u) (hw : EN N w) :
    EN N (s * w * si) := by
  obtain ⟨hO, hsq, hJ⟩ := hw
  obtain ⟨hre, hqf⟩ := pure_of_sqN N hN hsq
  have hsq' : (s * w * si) * (s * w * si) = -((N : ℚ) : PkgI1.B) := by
    calc (s * w * si) * (s * w * si) = s * (w * ((si * s) * (w * si))) := by simp only [mul_assoc]
      _ = s * (w * w) * si := by rw [hs.2.1, one_mul]; simp only [mul_assoc]
      _ = -((N : ℚ) : PkgI1.B) := by rw [hsq, mul_neg, neg_mul, scal_mid, hs.1, mul_one]
  refine ⟨(hs.2.2.1 w hO).1, hsq', ?_⟩
  obtain ⟨hre', hqf'⟩ := pure_of_sqN N hN hsq'
  refine imJ_pos_of_form (by rw [hqf']; exact hN) hb hb' ?_
  rw [hf w hre]
  exact form_pos (by rw [hqf]; exact hN) hu hJ hu'

theorem nat_of_int {x : ℚ} {m : ℤ} (h : x = m) (hp : 0 < x) : ∃ k : ℕ, x = k := by
  have hm : 0 ≤ m := by have := h ▸ hp; exact_mod_cast this.le
  exact ⟨m.toNat, by rw [h]; exact_mod_cast (Int.toNat_of_nonneg hm).symm⟩

theorem pure_coords {w : PkgI1.B} (hw : PkgI1.InO w) (hre : w.re = 0) :
    ∃ n0 n1 n3 : ℤ, w.imJ = -n0 ∧ w.imI = n1 + n3 / 2 ∧ w.imK = n3 / 2 := by
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff w).1 hw
  have h : (n2 : ℚ) = -2 * n0 := by have := hre; simp only at this; linarith
  exact ⟨n0, n1, n3, by simp only; rw [h]; ring, rfl, rfl⟩

/-! ### Orbit of `y` (`w² = −1`) -/

theorem orbit4 : ∀ w, EN 1 w → ∃ g gi, NormData g gi ∧ g * by4 * gi = w := by
  have hb : 0 < form by4 by4 := by norm_num [form, by4]
  have hb' : 0 < by4.imJ := by norm_num [by4]
  refine orbit_of_descent (EN 1) (fun w => form w by4) by4 ?_ ?_ ?_
  · intro w ⟨hO, hsq, hJ⟩
    obtain ⟨hre, hqf⟩ := pure_of_sqN 1 one_pos hsq
    obtain ⟨n0, n1, n3, hc, hb1, hd⟩ := pure_coords hO hre
    refine nat_of_int (m := -2 * n1 - n3 - 3 * n0) ?_ (form_pos (by rw [hqf]; norm_num) hb hJ hb')
    simp only [form, by4]; rw [hc, hb1]; push_cast; ring
  · intro w ⟨hO, hsq, hJ⟩ hle
    obtain ⟨hre, hqf⟩ := pure_of_sqN 1 one_pos hsq
    simp only [form, by4] at hle hqf
    norm_num at hle
    have h1 : w.imI = 1 := by nlinarith [sq_nonneg (w.imI - 1), sq_nonneg w.imK, sq_nonneg (3 * w.imJ - 1 - 2 * w.imI)]
    have h2 : w.imK = 0 := by nlinarith [sq_nonneg (w.imI - 1), sq_nonneg w.imK, sq_nonneg (3 * w.imJ - 1 - 2 * w.imI)]
    have h3 : w.imJ = 1 := by nlinarith [sq_nonneg (w.imI - 1), sq_nonneg w.imK, sq_nonneg (3 * w.imJ - 1 - 2 * w.imI)]
    ext <;> simp [by4, hre, h1, h2, h3]
  · intro w hw hlt
    obtain ⟨hO, hsq, hJ⟩ := hw
    obtain ⟨hre, hqf⟩ := pure_of_sqN 1 one_pos hsq
    obtain ⟨n0, n1, n3, hc, hb1, hd⟩ := pure_coords hO hre
    have hint : form w by4 = ((-2 * n1 - n3 - 3 * n0 : ℤ) : ℚ) := by
      simp only [form, by4]; rw [hc, hb1]; push_cast; ring
    have h2 : 2 ≤ form w by4 := by
      have h1 : form by4 by4 = 1 := by norm_num [form, by4]
      rw [h1, hint] at hlt; rw [hint]
      have : (1 : ℤ) < -2 * n1 - n3 - 3 * n0 := by exact_mod_cast hlt
      exact_mod_cast (show (2 : ℤ) ≤ -2 * n1 - n3 - 3 * n0 by omega)
    have e1 : ∀ v : PkgI1.B, v.re = 0 → form (a6 * v * a6i) by4 = form v ⟨0, 1/2, 1, -1/2⟩ := by
      intro v hv; simp [form, by4, a6, a6i, hv]; ring
    have e2 : ∀ v : PkgI1.B, v.re = 0 → form (a6i * v * a6) by4 = form v ⟨0, 1/2, 1, 1/2⟩ := by
      intro v hv; simp [form, by4, a6, a6i, hv]; ring
    have e3 : ∀ v : PkgI1.B, v.re = 0 →
        form (a6 * a4 * v * (a4i * a6i)) by4 = form v ⟨0, 7/2, 3, -1/2⟩ := by
      intro v hv; simp [form, by4, a6, a6i, a4, a4i, hv]; ring
    have e4 : ∀ v : PkgI1.B, v.re = 0 →
        form (a6i * a4i * v * (a4 * a6)) by4 = form v ⟨0, 7/2, 3, 1/2⟩ := by
      intro v hv; simp [form, by4, a6, a6i, a4, a4i, hv]; ring
    have hw : EN 1 w := ⟨hO, hsq, hJ⟩
    by_cases c1 : form w ⟨0, 1/2, 1, -1/2⟩ < form w by4
    · exact ⟨_, _, nd_a6, EN_conj one_pos nd_a6 (by norm_num [form]) (by norm_num) hb hb' e1 hw,
        by rw [e1 w hre]; exact c1⟩
    by_cases c2 : form w ⟨0, 1/2, 1, 1/2⟩ < form w by4
    · exact ⟨_, _, nd_a6.symm, EN_conj one_pos nd_a6.symm (by norm_num [form]) (by norm_num) hb hb'
        e2 hw, by rw [e2 w hre]; exact c2⟩
    by_cases c3 : form w ⟨0, 7/2, 3, -1/2⟩ < form w by4
    · exact ⟨_, _, nd_a6.mul nd_a4, EN_conj one_pos (nd_a6.mul nd_a4) (by norm_num [form])
        (by norm_num) hb hb' e3 hw, by rw [e3 w hre]; exact c3⟩
    by_cases c4 : form w ⟨0, 7/2, 3, 1/2⟩ < form w by4
    · exact ⟨_, _, nd_a6.symm.mul nd_a4.symm, EN_conj one_pos (nd_a6.symm.mul nd_a4.symm)
        (by norm_num [form]) (by norm_num) hb hb' e4 hw, by rw [e4 w hre]; exact c4⟩
    exfalso
    push_neg at c1 c2 c3 c4
    simp only [form, by4] at c1 c2 c3 c4 h2 hqf
    nlinarith [mul_nonneg (sub_nonneg.2 c1) (sub_nonneg.2 c4),
      mul_nonneg (sub_nonneg.2 c2) (sub_nonneg.2 c3)]

/-! ### Orbit of `j` (`w² = −3`) -/

theorem orbit3 : ∀ w, EN 3 w → ∃ g gi, NormData g gi ∧ g * bj * gi = w := by
  have hb : 0 < form bj bj := by norm_num [form, bj]
  have hb' : 0 < bj.imJ := by norm_num [bj]
  refine orbit_of_descent (EN 3) (fun w => form w bj) bj ?_ ?_ ?_
  · intro w ⟨hO, hsq, hJ⟩
    obtain ⟨hre, hqf⟩ := pure_of_sqN 3 (by norm_num) hsq
    obtain ⟨n0, n1, n3, hc, hb1, hd⟩ := pure_coords hO hre
    refine nat_of_int (m := -3 * n0) ?_ (form_pos (by rw [hqf]; norm_num) hb hJ hb')
    simp only [form, bj]; rw [hc]; push_cast; ring
  · intro w ⟨hO, hsq, hJ⟩ hle
    obtain ⟨hre, hqf⟩ := pure_of_sqN 3 (by norm_num) hsq
    simp only [form, bj] at hle hqf
    norm_num at hle
    have h3 : w.imJ ≤ 1 := by linarith
    have h1 : w.imI = 0 := by nlinarith [sq_nonneg w.imI, sq_nonneg w.imK]
    have h2 : w.imK = 0 := by nlinarith [sq_nonneg w.imI, sq_nonneg w.imK]
    have h4 : w.imJ = 1 := by nlinarith [sq_nonneg w.imI, sq_nonneg w.imK]
    ext <;> simp [bj, hre, h1, h2, h4]
  · intro w hw hlt
    obtain ⟨hO, hsq, hJ⟩ := hw
    obtain ⟨hre, hqf⟩ := pure_of_sqN 3 (by norm_num) hsq
    obtain ⟨n0, n1, n3, hc, hb1, hd⟩ := pure_coords hO hre
    have h2 : 2 ≤ w.imJ := by
      have h1 : form bj bj = 3 := by norm_num [form, bj]
      simp only [form, bj] at hlt; norm_num at hlt
      rw [hc] at hlt ⊢
      have : (1 : ℤ) < -n0 := by exact_mod_cast (show (1 : ℚ) < -(n0 : ℚ) by linarith)
      exact_mod_cast (show (2 : ℤ) ≤ -n0 by omega)
    have e1 : ∀ v : PkgI1.B, v.re = 0 → form (a4 * v * a4i) bj = form v ⟨0, 3, 3, -1⟩ := by
      intro v hv; simp [form, bj, a4, a4i, hv]; ring
    have e2 : ∀ v : PkgI1.B, v.re = 0 → form (a4i * v * a4) bj = form v ⟨0, 3, 3, 1⟩ := by
      intro v hv; simp [form, bj, a4, a4i, hv]; ring
    have e3 : ∀ v : PkgI1.B, v.re = 0 →
        form (a4 * a6 * v * (a6i * a4i)) bj = form v ⟨0, 0, 3, -2⟩ := by
      intro v hv; simp [form, bj, a6, a6i, a4, a4i, hv]; ring
    have e4 : ∀ v : PkgI1.B, v.re = 0 →
        form (a4i * a6i * v * (a6 * a4)) bj = form v ⟨0, 0, 3, 2⟩ := by
      intro v hv; simp [form, bj, a6, a6i, a4, a4i, hv]; ring
    have e5 : ∀ v : PkgI1.B, v.re = 0 →
        form (a4 * a6 * a6 * v * (a6i * (a6i * a4i))) bj = form v ⟨0, -3, 3, -1⟩ := by
      intro v hv; simp [form, bj, a6, a6i, a4, a4i, hv]; ring
    have e6 : ∀ v : PkgI1.B, v.re = 0 →
        form (a4i * a6i * a6i * v * (a6 * (a6 * a4))) bj = form v ⟨0, -3, 3, 1⟩ := by
      intro v hv; simp [form, bj, a6, a6i, a4, a4i, hv]; ring
    have hw : EN 3 w := ⟨hO, hsq, hJ⟩
    by_cases c1 : form w ⟨0, 3, 3, -1⟩ < form w bj
    · exact ⟨_, _, nd_a4, EN_conj (by norm_num : (0:ℚ) < 3) nd_a4 (by norm_num [form]) (by norm_num) hb hb' e1 hw,
        by rw [e1 w hre]; exact c1⟩
    by_cases c2 : form w ⟨0, 3, 3, 1⟩ < form w bj
    · exact ⟨_, _, nd_a4.symm, EN_conj (by norm_num : (0:ℚ) < 3) nd_a4.symm (by norm_num [form]) (by norm_num) hb hb' e2 hw,
        by rw [e2 w hre]; exact c2⟩
    by_cases c3 : form w ⟨0, 0, 3, -2⟩ < form w bj
    · exact ⟨_, _, (nd_a4.mul nd_a6), EN_conj (by norm_num : (0:ℚ) < 3) (nd_a4.mul nd_a6) (by norm_num [form]) (by norm_num) hb hb' e3 hw,
        by rw [e3 w hre]; exact c3⟩
    by_cases c4 : form w ⟨0, 0, 3, 2⟩ < form w bj
    · exact ⟨_, _, (nd_a4.symm.mul nd_a6.symm), EN_conj (by norm_num : (0:ℚ) < 3) (nd_a4.symm.mul nd_a6.symm) (by norm_num [form]) (by norm_num) hb hb' e4 hw,
        by rw [e4 w hre]; exact c4⟩
    by_cases c5 : form w ⟨0, -3, 3, -1⟩ < form w bj
    · exact ⟨_, _, ((nd_a4.mul nd_a6).mul nd_a6), EN_conj (by norm_num : (0:ℚ) < 3) ((nd_a4.mul nd_a6).mul nd_a6) (by norm_num [form]) (by norm_num) hb hb' e5 hw,
        by rw [e5 w hre]; exact c5⟩
    by_cases c6 : form w ⟨0, -3, 3, 1⟩ < form w bj
    · exact ⟨_, _, ((nd_a4.symm.mul nd_a6.symm).mul nd_a6.symm), EN_conj (by norm_num : (0:ℚ) < 3) ((nd_a4.symm.mul nd_a6.symm).mul nd_a6.symm) (by norm_num [form]) (by norm_num) hb hb' e6 hw,
        by rw [e6 w hre]; exact c6⟩
    exfalso
    push_neg at c1 c2 c3 c4 c5 c6
    simp only [form, bj] at c1 c2 c3 c4 c5 c6 hqf
    have h1 : 0 ≤ -w.imI + w.imJ + w.imK := by linarith
    have h2' : 0 ≤ -w.imI + w.imJ - w.imK := by linarith
    have h3 : 0 ≤ w.imJ + 2 * w.imK := by linarith
    have h4 : 0 ≤ w.imJ - 2 * w.imK := by linarith
    have h5 : 0 ≤ w.imI + w.imJ + w.imK := by linarith
    have h6 : 0 ≤ w.imI + w.imJ - w.imK := by linarith
    have : w.imJ ^ 2 ≤ -2 * w.imI ^ 2 + 3 * w.imJ ^ 2 - 6 * w.imK ^ 2 := by
      nlinarith [mul_nonneg h1 h6, mul_nonneg h2' h5, mul_nonneg h3 h4, mul_nonneg h1 h2',
        mul_nonneg h5 h6, mul_nonneg h1 h5, mul_nonneg h2' h6, mul_nonneg h3 h1, mul_nonneg h3 h2',
        mul_nonneg h3 h5, mul_nonneg h3 h6, mul_nonneg h4 h1, mul_nonneg h4 h2', mul_nonneg h4 h5,
        mul_nonneg h4 h6]
    nlinarith

/-! ### Orbit of `μ = 2j + ij` (`w² = −6`) -/

theorem orbit24 : ∀ w, EN 6 w → ∃ g gi, NormData g gi ∧ g * mu * gi = w := by
  have hb : 0 < form mu mu := by norm_num [form, mu]
  have hb' : 0 < mu.imJ := by norm_num [mu]
  refine orbit_of_descent (EN 6) (fun w => form w mu) mu ?_ ?_ ?_
  · intro w ⟨hO, hsq, hJ⟩
    obtain ⟨hre, hqf⟩ := pure_of_sqN 6 (by norm_num) hsq
    obtain ⟨n0, n1, n3, hc, hb1, hd⟩ := pure_coords hO hre
    refine nat_of_int (m := -6 * n0 - 3 * n3) ?_ (form_pos (by rw [hqf]; norm_num) hb hJ hb')
    simp only [form, mu]; rw [hc, hd]; push_cast; ring
  · intro w ⟨hO, hsq, hJ⟩ hle
    obtain ⟨hre, hqf⟩ := pure_of_sqN 6 (by norm_num) hsq
    simp only [form, mu] at hle hqf
    norm_num at hle
    have hcd : w.imJ ≤ w.imK + 1 := by linarith
    have hsq3 : w.imJ ^ 2 ≤ (w.imK + 1) ^ 2 := by
      have := mul_self_le_mul_self hJ.le hcd; nlinarith
    have h1 : w.imI = 0 := by nlinarith [sq_nonneg w.imI, sq_nonneg (w.imK - 1)]
    have h2 : w.imK = 1 := by nlinarith [sq_nonneg w.imI, sq_nonneg (w.imK - 1)]
    have h4 : w.imJ = 2 := by
      rw [h1, h2] at hqf; nlinarith
    ext <;> simp [mu, hre, h1, h2, h4]
  · intro w hw hlt
    obtain ⟨hO, hsq, hJ⟩ := hw
    obtain ⟨hre, hqf⟩ := pure_of_sqN 6 (by norm_num) hsq
    obtain ⟨n0, n1, n3, hc, hb1, hd⟩ := pure_coords hO hre
    have h2 : 3 ≤ 2 * w.imJ - 2 * w.imK := by
      simp only [form, mu] at hlt; norm_num at hlt
      rw [hc, hd] at hlt ⊢
      have : (2 : ℤ) < -2 * n0 - n3 := by
        exact_mod_cast (show (2 : ℚ) < -2 * (n0 : ℚ) - n3 by linarith)
      have h3 : (3 : ℤ) ≤ -2 * n0 - n3 := by omega
      have : (3 : ℚ) ≤ -2 * (n0 : ℚ) - n3 := by exact_mod_cast h3
      linarith
    have e1 : ∀ v : PkgI1.B, v.re = 0 → form (a6 * v * a6i) mu = form v ⟨0, 3/2, 2, 1/2⟩ := by
      intro v hv; simp [form, mu, a6, a6i, hv]; ring
    have e2 : ∀ v : PkgI1.B, v.re = 0 → form (a6i * v * a6) mu = form v ⟨0, -3/2, 2, 1/2⟩ := by
      intro v hv; simp [form, mu, a6, a6i, hv]; ring
    have e3 : ∀ v : PkgI1.B, v.re = 0 →
        form (a4 * a6i * a6i * v * (a6 * (a6 * a4i))) mu = form v ⟨0, 3/2, 4, 5/2⟩ := by
      intro v hv; simp [form, mu, a6, a6i, a4, a4i, hv]; ring
    have e4 : ∀ v : PkgI1.B, v.re = 0 →
        form (a6 * mu * v * (mui * a6i)) mu = form v ⟨0, -3/2, 4, 5/2⟩ := by
      intro v hv; simp [form, mu, mui, a6, a6i, hv]; ring
    have hw : EN 6 w := ⟨hO, hsq, hJ⟩
    by_cases c1 : form w ⟨0, 3/2, 2, 1/2⟩ < form w mu
    · exact ⟨_, _, nd_a6, EN_conj (by norm_num : (0:ℚ) < 6) nd_a6 (by norm_num [form]) (by norm_num) hb hb' e1 hw,
        by rw [e1 w hre]; exact c1⟩
    by_cases c2 : form w ⟨0, -3/2, 2, 1/2⟩ < form w mu
    · exact ⟨_, _, nd_a6.symm, EN_conj (by norm_num : (0:ℚ) < 6) nd_a6.symm (by norm_num [form]) (by norm_num) hb hb' e2 hw,
        by rw [e2 w hre]; exact c2⟩
    by_cases c3 : form w ⟨0, 3/2, 4, 5/2⟩ < form w mu
    · exact ⟨_, _, ((nd_a4.mul nd_a6.symm).mul nd_a6.symm), EN_conj (by norm_num : (0:ℚ) < 6) ((nd_a4.mul nd_a6.symm).mul nd_a6.symm) (by norm_num [form]) (by norm_num) hb hb' e3 hw,
        by rw [e3 w hre]; exact c3⟩
    by_cases c4 : form w ⟨0, -3/2, 4, 5/2⟩ < form w mu
    · exact ⟨_, _, (nd_a6.mul nd_mu), EN_conj (by norm_num : (0:ℚ) < 6) (nd_a6.mul nd_mu) (by norm_num [form]) (by norm_num) hb hb' e4 hw,
        by rw [e4 w hre]; exact c4⟩
    exfalso
    push_neg at c1 c2 c3 c4
    simp only [form, mu] at c1 c2 c3 c4 hqf
    have h1 : 0 ≤ -w.imI + w.imK := by linarith
    have h2' : 0 ≤ w.imI + w.imK := by linarith
    have h3 : 0 ≤ -w.imI + 2 * w.imJ - 3 * w.imK := by linarith
    have h4 : 0 ≤ w.imI + 2 * w.imJ - 3 * w.imK := by linarith
    have : 3 * (w.imJ - w.imK) ^ 2 ≤ -2 * w.imI ^ 2 + 3 * w.imJ ^ 2 - 6 * w.imK ^ 2 := by
      nlinarith [mul_nonneg h1 h4, mul_nonneg h2' h3, sq_nonneg w.imI]
    nlinarith

/-! ### `QMHauptmodul` from its values at three points -/

/-- `(1 + j)/2` (period-map's `x3`; `x3² − x3 + 1 = 0`). -/
def x3 : PkgI1.B := ⟨1 / 2, 0, 1 / 2, 0⟩

/-- **LEAF candidate (narrowed `QMHauptmodul`).** `PkgI1.QMHauptmodul` with each of its three CM clauses
asserted only at the fixed points of `ι(x)` for one element: `x = i + j` (`x² = −1`), `x = (1 + j)/2`
(`x² − x + 1 = 0`) and `x = 2j + ij` (`x² = −6`), the elliptic points `√2 + i`, `i√3`, `i√(9 + 6√2)` of
orders 4, 6, 2. Weaker than `QMHauptmodul`; `qmHauptmodul_of_base` recovers it, because the CM points of
each discriminant form one `Γ*`-orbit (`orbit4`, `orbit3`, `orbit24`). -/
def QMHauptmodulBase : Prop :=
  ∃ f : UpperHalfPlane → OnePoint ℂ, Continuous f ∧
    (∀ τ : UpperHalfPlane, PkgI1.jDen (PkgI1.Omega τ) ≠ 0 →
      f τ = ((PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) : ℂ) : OnePoint ℂ)) ∧
    (∀ τ τ' : UpperHalfPlane, f τ = f τ' ↔ ∃ γ ∈ PkgI1.GammaStar, γ • τ = τ') ∧
    Function.Surjective f ∧
    (∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota by4 →
      ∀ τ : UpperHalfPlane, γ • τ = τ → f τ = ((0 : ℂ) : OnePoint ℂ)) ∧
    (∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x3 →
      ∀ τ : UpperHalfPlane, γ • τ = τ → f τ = (OnePoint.infty : OnePoint ℂ)) ∧
    (∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu →
      ∀ τ : UpperHalfPlane, γ • τ = τ → f τ = ((-16/27 : ℂ) : OnePoint ℂ))

theorem det_ne' {x : PkgI1.B} (h : nrd x ≠ 0) : (PkgI1.iota x).det ≠ 0 := by
  rw [det_iota_eq]; exact_mod_cast h

/-- The element of `GL₂(ℝ)` with matrix `ι(x)`. -/
noncomputable def glOf (x : PkgI1.B) (h : nrd x ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (PkgI1.iota x) (det_ne' h)

theorem coe_glOf (x : PkgI1.B) (h : nrd x ≠ 0) :
    (glOf x h : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x := rfl

theorem iota_one : PkgI1.iota 1 = 1 := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem glOf_mem {g gi : PkgI1.B} (hg : NormData g gi) : glOf g hg.2.2.2.ne' ∈ PkgI1.GammaStar :=
  ⟨g, ⟨gi, hg.1, hg.2.1, hg.2.2.1⟩, rfl, by rw [coe_glOf, det_iota_eq]; exact_mod_cast hg.2.2.2⟩

/-- **The transfer step.** If `f` is constant on `Γ*`-orbits and takes the value `val` at the fixed points
of `ι(b)`, it takes `val` at the fixed points of `ι(g b g⁻¹)` for every normalizer `g`. -/
theorem transfer {f : UpperHalfPlane → OnePoint ℂ}
    (hfib : ∀ τ τ' : UpperHalfPlane, f τ = f τ' ↔ ∃ γ ∈ PkgI1.GammaStar, γ • τ = τ')
    {b : PkgI1.B} {val : OnePoint ℂ}
    (hbase : ∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota b →
      ∀ τ : UpperHalfPlane, γ • τ = τ → f τ = val)
    {g gi : PkgI1.B} (hg : NormData g gi) (γ₁ : GL (Fin 2) ℝ)
    (hγ₁ : (γ₁ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota (g * b * gi)) (τ : UpperHalfPlane)
    (hτ : γ₁ • τ = τ) : f τ = val := by
  have hgi := hg.symm
  set G := glOf g hg.2.2.2.ne'
  set G' := glOf gi hgi.2.2.2.ne'
  have hGG' : G * G' = 1 := by
    ext1; rw [Units.val_mul, coe_glOf, coe_glOf, ← iota_mul, hg.1, iota_one]; rfl
  have hval := hbase (G' * γ₁ * G) (by
    rw [Units.val_mul, Units.val_mul, coe_glOf, coe_glOf, hγ₁, ← iota_mul, ← iota_mul]
    congr 1
    calc gi * (g * b * gi) * g = (gi * g) * b * (gi * g) := by simp only [mul_assoc]
      _ = b := by rw [hg.2.1, one_mul, mul_one]) (G' • τ) (by
    rw [mul_smul, mul_smul, ← mul_smul G G', hGG', one_smul, hτ])
  rw [← hval]
  exact (hfib τ (G' • τ)).2 ⟨G', glOf_mem hgi, rfl⟩ |>.symm.symm

theorem inO_neg {x : PkgI1.B} (h : PkgI1.InO x) : PkgI1.InO (-x) := by
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff x).1 h
  exact (inO_iff _).2 ⟨-n0, -n1, -n2, -n3, by ext <;> simp <;> ring⟩

theorem inO_two_sub {x : PkgI1.B} (h : PkgI1.InO x) : PkgI1.InO (2 * x - 1) := by
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff x).1 h
  refine (inO_iff _).2 ⟨2 * n0 - 1, 2 * n1, 2 * n2, 2 * n3, ?_⟩
  ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat,
    QuaternionAlgebra.imK_ofNat] <;> ring

theorem imJ_ne_zero {N : ℚ} (hN : 0 < N) {v : PkgI1.B} (h : v * v = -((N : ℚ) : PkgI1.B)) :
    v.imJ ≠ 0 := by
  obtain ⟨-, hq⟩ := pure_of_sqN N hN h
  intro h0; simp [form, h0] at hq; nlinarith [sq_nonneg v.imI, sq_nonneg v.imK]

/-- An upper-sheet representative of `±v`. -/
theorem upper_of {N : ℚ} (hN : 0 < N) {v : PkgI1.B} (hO : PkgI1.InO v)
    (h : v * v = -((N : ℚ) : PkgI1.B)) : EN N v ∨ EN N (-v) := by
  rcases lt_or_gt_of_ne (imJ_ne_zero hN h) with hl | hl
  · right; exact ⟨inO_neg hO, by rw [neg_mul_neg, h], by simpa using hl⟩
  · left; exact ⟨hO, h, hl⟩

theorem iota_neg (x : PkgI1.B) : PkgI1.iota (-x) = -PkgI1.iota x := by
  rw [iota_apply, iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem neg_one_sq_cast : -((1 : ℚ) : PkgI1.B) = -1 := by simp

/-- **`QMHauptmodul` from `QMHauptmodulBase` (proved).** -/
theorem qmHauptmodul_of_base (h : QMHauptmodulBase) : PkgI1.QMHauptmodul := by
  obtain ⟨f, hc, hform, hfib, hsurj, h4, h3, h24⟩ := h
  refine ⟨f, hc, hform, hfib, hsurj, ?_, ?_, ?_⟩
  · intro x hO hx γ hγ τ hτ
    have hx' : x * x = -((1 : ℚ) : PkgI1.B) := by rw [hx]; simp
    rcases upper_of one_pos hO hx' with hE | hE
    · obtain ⟨g, gi, hg, hgx⟩ := orbit4 x hE
      exact transfer hfib h4 hg γ (by rw [hgx, hγ]) τ hτ
    · obtain ⟨g, gi, hg, hgx⟩ := orbit4 (-x) hE
      exact transfer hfib h4 hg (-γ) (by rw [hgx, iota_neg, Units.val_neg, hγ]) τ
        (by rw [UpperHalfPlane.neg_smul, hτ])
  · intro x hO hx γ hγ τ hτ
    have hw : (2 * x - 1) * (2 * x - 1) = -((3 : ℚ) : PkgI1.B) := by
      have : (2 * x - 1) * (2 * x - 1) = 4 * (x * x - x + 1) - 3 := by
        ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
          QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring
      rw [this, hx]; simp
    have hx1 : x * (1 - x) = 1 := by
      have : x * (1 - x) = -(x * x - x + 1) + 1 := by noncomm_ring
      rw [this, hx, neg_zero, zero_add]
    rcases upper_of (by norm_num : (0 : ℚ) < 3) (inO_two_sub hO) hw with hE | hE
    · obtain ⟨g, gi, hg, hgx⟩ := orbit3 _ hE
      have hgx3 : g * x3 * gi = x := by
        have e : x3 = (1 / 2 : ℚ) • (1 + bj) := by ext <;> simp [x3, bj]
        have : g * x3 * gi = (1 / 2 : ℚ) • (g * gi + g * bj * gi) := by
          rw [e]; simp only [mul_add, add_mul, mul_one, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        rw [this, hg.1, hgx]
        ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
          QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring
      exact transfer hfib h3 hg γ (by rw [hgx3, hγ]) τ hτ
    · obtain ⟨g, gi, hg, hgx⟩ := orbit3 _ hE
      have hgx3 : g * x3 * gi = 1 - x := by
        have e : x3 = (1 / 2 : ℚ) • (1 + bj) := by ext <;> simp [x3, bj]
        have : g * x3 * gi = (1 / 2 : ℚ) • (g * gi + g * bj * gi) := by
          rw [e]; simp only [mul_add, add_mul, mul_one, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        rw [this, hg.1, hgx]
        ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
          QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring
      have hinv : ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota (1 - x) := by
        have h1 : (γ : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota (1 - x) = 1 := by
          rw [hγ, ← iota_mul, hx1, iota_one]
        calc ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
            = ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
                ((γ : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota (1 - x)) := by rw [h1, mul_one]
          _ = PkgI1.iota (1 - x) := by
            rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      exact transfer hfib h3 hg γ⁻¹ (by rw [hgx3, hinv]) τ (by
        conv_lhs => rw [← hτ]
        rw [inv_smul_smul])
  · intro x hO hx γ hγ τ hτ
    have hx' : x * x = -((6 : ℚ) : PkgI1.B) := by rw [hx]; simp
    rcases upper_of (by norm_num : (0 : ℚ) < 6) hO hx' with hE | hE
    · obtain ⟨g, gi, hg, hgx⟩ := orbit24 x hE
      exact transfer hfib h24 hg γ (by rw [hgx, hγ]) τ hτ
    · obtain ⟨g, gi, hg, hgx⟩ := orbit24 (-x) hE
      exact transfer hfib h24 hg (-γ) (by rw [hgx, iota_neg, Units.val_neg, hγ]) τ
        (by rw [UpperHalfPlane.neg_smul, hτ])

end HDec.LeafQCheck.HM

/-! ### Weight 20: `∏θ_m² ∘ Ω` (period-glue's `G8` machinery with `ThetaModularity`'s second clause)

Copied from `scratch/leaf-fold4/Leaves4.lean` (period-glue, lines 116948-117320) with `G8 → G20`,
`thetaSum8 → thetaProd2`, exponents `4, 8 → 10, 20` and the first clause of `ThetaModularity` replaced by
the second. -/

namespace HDec.HSyn.G0Split.FibreQM.PeriodGlue.LQ20
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)
open Complex Matrix HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMap HSyn.G0Split.FibreQM.PeriodGlue
open UpperHalfPlane (num denom σ coe_smul_of_det_pos denom_ne_zero)

/-- `Π/dF¹⁰ = ∏θ_m²(Ω(τ)) / ((τ − 3)(τ + 1))¹⁰`, a weight-20 automorphic form of `Γ*`. -/
noncomputable def G20 (z : ℂ) : ℂ := PkgI1.thetaProd2 (PkgI1.Omega z) / ((z - 3) * (z + 1)) ^ 10


/-- `g ∈ GL₂(ℝ)⁺` and `G20` has the exact automorphy of `S8WeightExact` for `g`. -/
def G20Auto (γ : GL (Fin 2) ℝ) : Prop :=
  0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det ∧ ∀ z : UpperHalfPlane,
    G20 ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ 10 =
      denom γ z ^ 20 * G20 (z : ℂ)

theorem g20Auto_one : G20Auto 1 := by
  refine ⟨by simp, fun z => ?_⟩
  simp [UpperHalfPlane.denom]

theorem g20Auto_mul {g h : GL (Fin 2) ℝ} (hg : G20Auto g) (hh : G20Auto h) : G20Auto (g * h) := by
  refine ⟨by rw [Units.val_mul, det_mul]; exact mul_pos hg.1 hh.1, fun z => ?_⟩
  rw [mul_smul, denom_mul_pos g h hh.1, Units.val_mul, det_mul]
  have e1 := hg.2 (h • z)
  have e2 := hh.2 z
  push_cast
  calc G20 ((g • h • z : UpperHalfPlane) : ℂ) *
        (((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) * ((h : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ)) ^ 10
      = (G20 ((g • h • z : UpperHalfPlane) : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 10) *
          ((h : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 10 := by ring
    _ = denom g ((h • z : UpperHalfPlane) : ℂ) ^ 20 * (G20 ((h • z : UpperHalfPlane) : ℂ) *
          ((h : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 10) := by rw [e1]; ring
    _ = _ := by rw [e2]; ring

theorem g20Auto_inv {g : GL (Fin 2) ℝ} (hg : G20Auto g) : G20Auto g⁻¹ := by
  have hd : ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det)⁻¹ := by
    rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  refine ⟨by rw [hd]; exact inv_pos.mpr hg.1, fun z => ?_⟩
  set z' := g⁻¹ • z with hz'
  have e := hg.2 z'
  rw [hz', smul_inv_smul] at e
  have hc := denom_mul_pos g g⁻¹ (by rw [hd]; exact inv_pos.mpr hg.1) z
  rw [mul_inv_cancel] at hc
  have h1 : denom (1 : GL (Fin 2) ℝ) z = 1 := by simp [UpperHalfPlane.denom]
  rw [h1] at hc
  have hD : denom g ((g⁻¹ • z : UpperHalfPlane) : ℂ) ≠ 0 := denom_ne_zero _ _
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ≠ 0 := by exact_mod_cast hg.1.ne'
  rw [hd]
  push_cast
  have key : G20 ((g⁻¹ • z : UpperHalfPlane) : ℂ) = G20 (z : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 10 /
      denom g ((g⁻¹ • z : UpperHalfPlane) : ℂ) ^ 20 := by
    rw [eq_div_iff (pow_ne_zero _ hD), e]; ring
  rw [key]
  have hinv : denom g⁻¹ z = (denom g ((g⁻¹ • z : UpperHalfPlane) : ℂ))⁻¹ :=
    (eq_inv_of_mul_eq_one_right hc.symm)
  rw [hinv]
  field_simp

theorem g20Auto_scalar {g : GL (Fin 2) ℝ} (q : ℚ) (hq : q ≠ 0)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = (q : ℝ) • 1) : G20Auto g := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = (q : ℝ) ^ 2 := by
    rw [hg, Matrix.det_smul, Matrix.det_one]; simp
  have hpos : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; positivity
  have e00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = q := by rw [hg]; simp
  have e01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by rw [hg]; simp
  have e10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by rw [hg]; simp
  have e11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = q := by rw [hg]; simp
  refine ⟨hpos, fun z => ?_⟩
  have hden : denom g z = (q : ℂ) := by simp [UpperHalfPlane.denom, e10, e11]
  have hsm : g • z = z := by
    ext1
    rw [coe_smul_of_det_pos (by rwa [detv]), hden]
    simp only [UpperHalfPlane.num, e00, e01]
    have : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    field_simp
    push_cast; ring
  rw [hsm, hden, hdet]
  push_cast; ring

/-- The automorphy group of `G20` (a subgroup of `GL₂(ℝ)⁺`). -/
def G20AutoSubgroup : Subgroup (GL (Fin 2) ℝ) where
  carrier := {γ | G20Auto γ}
  one_mem' := g20Auto_one
  mul_mem' := g20Auto_mul
  inv_mem' := g20Auto_inv

theorem g20Auto_of_sp (hT : PkgI1.ThetaModularity) (g : GL (Fin 2) ℝ)
    (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    (hrel : ∀ z : ℂ, 0 < z.im →
      PkgI1.spAct M (PkgI1.Omega z) = PkgI1.Omega (num g z / denom g z))
    (ε : ℂ) (hε : ε ^ 10 = 1)
    (hfac : ∀ z : ℂ, 0 < z.im →
      PkgI1.spFactor M (PkgI1.Omega z) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
        ((z - 3) * (z + 1)) =
      ε * denom g z ^ 2 * ((num g z / denom g z - 3) * (num g z / denom g z + 1))) :
    G20Auto g := by
  refine ⟨hdet, fun z => ?_⟩
  have hw : ((g • z : UpperHalfPlane) : ℂ) = num g z / denom g z :=
    coe_smul_of_det_pos (by rwa [detv]) z
  have hwim : 0 < (num g z / denom g z).im := by rw [← hw]; exact (g • z).im_pos
  have hmod := (hT M hM (PkgI1.Omega z) (omegaSiegel_proof z z.im_pos)).2
  rw [hrel z z.im_pos] at hmod
  have hf := hfac z z.im_pos
  unfold G20
  rw [hw, hmod]
  have hf10 : (PkgI1.spFactor M (PkgI1.Omega z) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
      ((z - 3) * (z + 1))) ^ 10 =
      (denom g z ^ 2 * ((num g z / denom g z - 3) * (num g z / denom g z + 1))) ^ 10 := by
    rw [hf, mul_assoc, mul_pow, hε, one_mul]
  obtain ⟨h3, h4⟩ := sub3_add1_ne z.im_pos
  obtain ⟨h5, h6⟩ := sub3_add1_ne hwim
  have hD : denom g z ≠ 0 := denom_ne_zero g z
  have hW : ((num g z / denom g z - 3) * (num g z / denom g z + 1)) ^ 10 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero h5 h6)
  have hZ : (((z : ℂ) - 3) * ((z : ℂ) + 1)) ^ 10 ≠ 0 := pow_ne_zero _ (mul_ne_zero h3 h4)
  rw [div_mul_eq_mul_div, mul_div_assoc', div_eq_div_iff hW hZ]
  linear_combination (PkgI1.thetaProd2 (PkgI1.Omega z)) * hf10

theorem g20Auto_gen (hT : PkgI1.ThetaModularity) (g : GL (Fin 2) ℝ)
    (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (hMs : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    (A B C D : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A B C D)
    (hI1 : ∀ z : ℂ, dFh (num g z) (denom g z) • (A * Nf z + dF z • B) =
      Nfh (num g z) (denom g z) * (C * Nf z + dF z • D))
    (hI2 : ∀ z : ℂ, (C * Nf z + dF z • D).det * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
      ((z - 3) * (z + 1)) = -1 * dF z ^ 2 * ((num g z - 3 * denom g z) * (num g z + denom g z))) :
    G20Auto g := by
  have hw : ∀ z : ℂ, 0 < z.im → 0 < (num g z / denom g z).im := fun z hz => by
    have := (g • (⟨z, hz⟩ : UpperHalfPlane)).im_pos
    rwa [← UpperHalfPlane.coe_im, coe_smul_of_det_pos (by rwa [detv])] at this
  have hV : ∀ z : ℂ, 0 < z.im → denom g z ≠ 0 := fun z hz =>
    UpperHalfPlane.denom_ne_zero_of_im g hz.ne'
  have hP : ∀ z : ℂ, 0 < z.im → (C * Nf z + dF z • D).det ≠ 0 := fun z hz h0 => by
    have e := hI2 z
    rw [h0, zero_mul, zero_mul] at e
    obtain ⟨h5, h6⟩ := sub3_add1_ne (hw z hz)
    have h7 : num g z - 3 * denom g z ≠ 0 := fun h => h5 (by
      rw [show num g z = 3 * denom g z by linear_combination h, mul_div_assoc,
        div_self (hV z hz)]; ring)
    have h8 : num g z + denom g z ≠ 0 := fun h => h6 (by
      rw [show num g z = -denom g z by linear_combination h, neg_div, div_self (hV z hz)]; ring)
    have := dF_ne hz
    have : -1 * dF z ^ 2 * ((num g z - 3 * denom g z) * (num g z + denom g z)) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ this)) (mul_ne_zero h7 h8)
    exact this e.symm
  refine g20Auto_of_sp hT g hdet M hMs (fun z hz => ?_) (-1) (by norm_num) (fun z hz => ?_)
  · exact spAct_of_poly M A B C D hM z _ _ (hV z hz) (dF_ne hz) (dF_ne (hw z hz)) (hP z hz) (hI1 z)
  · exact spFactor_of_poly M A B C D hM z _ _ _ (hV z hz) (dF_ne hz) (hI2 z)

theorem iota_x4 : PkgI1.iota x4 = !![1 + √2, -3; 1, 1 - √2] := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [x4]

theorem iota_x6 : PkgI1.iota x6 = !![-3 / 2, -3 / 2; 1 / 2, -3 / 2] := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [x6] <;> norm_num

theorem g20Auto_g4 (hT : PkgI1.ThetaModularity) {g : GL (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x4) : G20Auto g := by
  rw [iota_x4] at hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 2 := by
    rw [hg, Matrix.det_fin_two_of]; linear_combination (-1 : ℝ) * sqrt2_sq'
  have hnum : ∀ z : ℂ, num g z = (√2 : ℂ) * z + z - 3 := fun z => by
    simp only [UpperHalfPlane.num, hg]; simp; ring
  have hden : ∀ z : ℂ, denom g z = -(√2 : ℂ) + z + 1 := fun z => by
    simp only [UpperHalfPlane.denom, hg]; simp; ring
  refine g20Auto_gen hT g (by rw [hdet]; norm_num) M4 M4_symp A4 B4 C4 D4 M4_map
    (fun z => by rw [hnum, hden]; exact I1_g4 z) (fun z => ?_)
  rw [hnum, hden, hdet]; push_cast; exact I2_g4 z

theorem g20Auto_g6 (hT : PkgI1.ThetaModularity) {g : GL (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x6) : G20Auto g := by
  rw [iota_x6] at hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 3 := by
    rw [hg, Matrix.det_fin_two_of]; norm_num
  have hnum : ∀ z : ℂ, num g z = -3 * z / 2 - 3 / 2 := fun z => by
    simp only [UpperHalfPlane.num, hg]; simp; ring
  have hden : ∀ z : ℂ, denom g z = z / 2 - 3 / 2 := fun z => by
    simp only [UpperHalfPlane.denom, hg]; simp; ring
  refine g20Auto_gen hT g (by rw [hdet]; norm_num) M6 M6_symp A6 B6 C6 D6 M6_map
    (fun z => by rw [hnum, hden]; exact I1_g6 z) (fun z => ?_)
  rw [hnum, hden, hdet]; push_cast; exact I2_g6 z

/-- **The exact weight-20 automorphy of `G20` on all of `Γ*`** (from R4 and `GammaStarGen`). -/
theorem s20WeightExact_of (hT : PkgI1.ThetaModularity) (hG : GammaStarGen) :
    ∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
      G20 ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ 10 =
        denom γ z ^ 20 * G20 (z : ℂ) := by
  intro γ hγ z
  have hmem : γ ∈ G20AutoSubgroup := by
    refine (Subgroup.closure_le (K := G20AutoSubgroup)).mpr ?_ (hG γ hγ)
    rintro g ((hg | hg) | ⟨q, hq, hg⟩)
    · exact g20Auto_g4 hT hg
    · exact g20Auto_g6 hT hg
    · exact g20Auto_scalar q hq hg
  exact hmem.2 z

end HDec.HSyn.G0Split.FibreQM.PeriodGlue.LQ20

namespace HDec.LeafQCheck.HM

open PkgI1

/-! ### The disc −4 clause is a computation: `j_θ(√2 + i) = 0` -/

open HSyn.G0Split.FibreQM.PeriodGlue (th1 thT thetaConst_factor Omega0 omega_cm4 s8Omega0_proof τ1 τ2)

/-- The odd one-variable theta constant `Θ[1,1](τ)` vanishes (`n ↦ −n − 1`). -/
theorem th1_one_one (τ : ℂ) : th1 1 1 τ = 0 := by
  let e : ℤ ≃ ℤ := ⟨fun n => -n - 1, fun n => -n - 1, fun n => by ring, fun n => by ring⟩
  have hfe : ∀ n, thT 1 1 τ (e n) = -thT 1 1 τ n := by
    intro n
    simp only [thT, e, Equiv.coe_fn_mk]
    have : Real.pi * Complex.I * (((-n - 1 : ℤ) : ℂ) + ((1 : ℕ) : ℂ) / 2) ^ 2 * τ +
        Real.pi * Complex.I * (((-n - 1 : ℤ) : ℂ) + ((1 : ℕ) : ℂ) / 2) * ((1 : ℕ) : ℂ) =
        (Real.pi * Complex.I * ((n : ℂ) + ((1 : ℕ) : ℂ) / 2) ^ 2 * τ +
          Real.pi * Complex.I * ((n : ℂ) + ((1 : ℕ) : ℂ) / 2) * ((1 : ℕ) : ℂ)) +
        ((-2 * n - 1 : ℤ) : ℂ) * (Real.pi * Complex.I) := by push_cast; ring
    rw [this, Complex.exp_add, HSyn.G0Split.FibreQM.PeriodGlue.exp_int_piI]
    have h2 : ((-1 : ℂ)) ^ (-2 * n - 1) = -1 := by
      rw [zpow_sub₀ (by norm_num), zpow_mul, zpow_neg, zpow_one]
      norm_num
    rw [h2]; ring
  have h := e.tsum_eq (thT 1 1 τ)
  simp only [hfe, tsum_neg] at h
  unfold th1
  linear_combination -h / 2

theorem thetaProd2_omega0 : PkgI1.thetaProd2 Omega0 = 0 := by
  unfold PkgI1.thetaProd2
  apply Finset.prod_eq_zero (i := (![1, 1], ![0, 0])) (by decide)
  rw [thetaConst_factor]
  simp [th1_one_one]

theorem jNum_tau4 : PkgI1.jNum (PkgI1.Omega ((√2 : ℂ) + Complex.I)) = 0 := by
  rw [omega_cm4]; unfold PkgI1.jNum; rw [thetaProd2_omega0]; ring

theorem jDen_tau4 : PkgI1.jDen (PkgI1.Omega ((√2 : ℂ) + Complex.I)) ≠ 0 := by
  rw [omega_cm4]; unfold PkgI1.jDen; exact pow_ne_zero _ s8Omega0_proof

/-- The fixed point of `ι(i + j)` in `ℍ` is `√2 + i`. -/
theorem fixed_by4 {γ : GL (Fin 2) ℝ} (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota by4)
    {τ : UpperHalfPlane} (hτ : γ • τ = τ) : (τ : ℂ) = (√2 : ℂ) + Complex.I := by
  have hM : (γ : Matrix (Fin 2) (Fin 2) ℝ) = !![√2, -3; 1, -√2] := by
    rw [hγ, iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [by4]
  have hdet : 0 < γ.det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hM, Matrix.det_fin_two_of]
    nlinarith [sqrt2_sq']
  have h := congrArg (fun w : UpperHalfPlane => (w : ℂ)) hτ
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet, div_eq_iff (UpperHalfPlane.denom_ne_zero γ τ)] at h
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hM, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons] at h
  have s2 : (√2 : ℂ) * √2 = 2 := by
    rw [← Complex.ofReal_mul, sqrt2_sq']; norm_num
  have hq : ((τ : ℂ) - √2 - Complex.I) * ((τ : ℂ) - √2 + Complex.I) = 0 := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast at h
    linear_combination (-1 : ℂ) * h + s2 - hI
  rcases mul_eq_zero.1 hq with h1 | h1
  · linear_combination h1
  · exfalso
    have := congrArg Complex.im h1
    simp at this
    linarith [τ.im_pos]

/-- **`QMHauptmodulBase` without its disc −4 clause.** The value `0` at `√2 + i` follows from the formula
clause, since `∏θ_m(Ω(√2+i)) = 0` (the characteristic `((1,1),(0,0))`, `Ω(√2+i)` being a product
matrix) and `Σθ⁸(Ω(√2+i)) ≠ 0` (period-glue's certified `S8Omega0`). -/
def QMHauptmodulBase2 : Prop :=
  ∃ f : UpperHalfPlane → OnePoint ℂ, Continuous f ∧
    (∀ τ : UpperHalfPlane, PkgI1.jDen (PkgI1.Omega τ) ≠ 0 →
      f τ = ((PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) : ℂ) : OnePoint ℂ)) ∧
    (∀ τ τ' : UpperHalfPlane, f τ = f τ' ↔ ∃ γ ∈ PkgI1.GammaStar, γ • τ = τ') ∧
    Function.Surjective f ∧
    (∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x3 →
      ∀ τ : UpperHalfPlane, γ • τ = τ → f τ = (OnePoint.infty : OnePoint ℂ)) ∧
    (∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu →
      ∀ τ : UpperHalfPlane, γ • τ = τ → f τ = ((-16/27 : ℂ) : OnePoint ℂ))

theorem base_of_base2 (h : QMHauptmodulBase2) : QMHauptmodulBase := by
  obtain ⟨f, hc, hform, hfib, hsurj, h3, h24⟩ := h
  refine ⟨f, hc, hform, hfib, hsurj, fun γ hγ τ hτ => ?_, h3, h24⟩
  have hτ4 := fixed_by4 hγ hτ
  have hd : PkgI1.jDen (PkgI1.Omega τ) ≠ 0 := by rw [hτ4]; exact jDen_tau4
  rw [hform τ hd, hτ4, jNum_tau4, zero_div]

/-- **`QMHauptmodul` from `QMHauptmodulBase2` (proved).** -/
theorem qmHauptmodul_of_base2 (h : QMHauptmodulBase2) : PkgI1.QMHauptmodul :=
  qmHauptmodul_of_base (base_of_base2 h)

/-! ### The disc −3 clause from the valence bound: the pole of `j_θ` at `i√3` -/

open HSyn.G0Split.FibreQM.PeriodMap (G8 U tau3 tau4 thetaOmegaAnalytic_proof s8OrderCM3_of
  ValenceBoundGammaStar isOpen_U isPreconnected_U)

/-- `Σθ⁸ ∘ Ω`. -/
noncomputable def Sf (z : ℂ) : ℂ := PkgI1.thetaSum8 (PkgI1.Omega z)
/-- `∏θ² ∘ Ω`. -/
noncomputable def Pf (z : ℂ) : ℂ := PkgI1.thetaProd2 (PkgI1.Omega z)
/-- `(z − 3)(z + 1)`. -/
def Zf (z : ℂ) : ℂ := (z - 3) * (z + 1)

theorem Zf_ne {z : ℂ} (hz : 0 < z.im) : Zf z ≠ 0 := by
  unfold Zf
  have h3 : z - 3 ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
  have h4 : z + 1 ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
  exact mul_ne_zero h3 h4

theorem Zf_analytic (z : ℂ) : AnalyticAt ℂ Zf z := by unfold Zf; fun_prop

theorem Sf_analytic : AnalyticOnNhd ℂ Sf U := thetaOmegaAnalytic_proof.1
theorem Pf_analytic : AnalyticOnNhd ℂ Pf U := thetaOmegaAnalytic_proof.2

theorem jDenO_eq (z : ℂ) : PkgI1.jDen (PkgI1.Omega z) = Sf z ^ 5 := rfl
theorem jNumO_eq (z : ℂ) : PkgI1.jNum (PkgI1.Omega z) = 3779136 * Pf z ^ 2 := rfl

theorem tau4_coe : (tau4 : ℂ) = (√2 : ℂ) + Complex.I := rfl
theorem tau3_coe : (tau3 : ℂ) = (√3 : ℂ) * Complex.I := rfl

theorem Sf_tau4 : Sf (tau4 : ℂ) ≠ 0 := by
  unfold Sf; rw [tau4_coe, omega_cm4]; exact s8Omega0_proof

theorem Pf_tau4 : Pf (tau4 : ℂ) = 0 := by
  unfold Pf; rw [tau4_coe, omega_cm4]; exact thetaProd2_omega0

/-- `jDen ∘ Ω` is analytic on `ℍ` and nowhere locally zero. -/
theorem jDenO_analytic : AnalyticOnNhd ℂ (fun z => PkgI1.jDen (PkgI1.Omega z)) U :=
  fun z hz => (Sf_analytic z hz).pow 5

theorem jDenO_order_ne_top {z : ℂ} (hz : z ∈ U) :
    analyticOrderAt (fun z => PkgI1.jDen (PkgI1.Omega z)) z ≠ ⊤ := by
  intro htop
  have hev := analyticOrderAt_eq_top.1 htop
  have h0 := jDenO_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_U hz hev
  have h4 := h0 (show (tau4 : ℂ) ∈ U from tau4.im_pos)
  simp only [Pi.zero_apply, jDenO_eq] at h4
  exact Sf_tau4 (pow_eq_zero_iff (by norm_num) |>.1 h4)

/-- Near every point of `ℍ`, `jDen ∘ Ω ≠ 0` off that point. -/
theorem jDenO_eventually_ne {z : ℂ} (hz : z ∈ U) :
    ∀ᶠ w in nhdsWithin z {z}ᶜ, PkgI1.jDen (PkgI1.Omega w) ≠ 0 := by
  rcases (jDenO_analytic z hz).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (analyticOrderAt_eq_top.2 h) (jDenO_order_ne_top hz)
  · exact h

open Filter Topology in
theorem map_coe_punctured (τ0 : UpperHalfPlane) :
    Filter.map (fun τ : UpperHalfPlane => (τ : ℂ)) (𝓝[≠] τ0) = 𝓝[≠] (τ0 : ℂ) := by
  rw [UpperHalfPlane.isOpenEmbedding_coe.map_nhdsWithin_eq]
  have himg : (fun τ : UpperHalfPlane => (τ : ℂ)) '' {τ0}ᶜ = U ∩ {(τ0 : ℂ)}ᶜ := by
    ext z
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨τ.im_pos, fun h => hτ (UpperHalfPlane.ext h)⟩
    · rintro ⟨hz, hne⟩
      exact ⟨⟨z, hz⟩, fun h => hne (by rw [← h]; rfl), rfl⟩
  rw [himg, nhdsWithin_inter_of_mem]
  exact mem_nhdsWithin_of_mem_nhds (isOpen_U.mem_nhds τ0.im_pos)

open Filter Topology in
instance punctured_neBot (τ0 : UpperHalfPlane) : (𝓝[≠] τ0).NeBot := by
  rw [← Filter.map_neBot_iff (fun τ : UpperHalfPlane => (τ : ℂ)), map_coe_punctured]
  infer_instance

open Filter Topology in
theorem eventually_jDen_ne_H (τ0 : UpperHalfPlane) :
    ∀ᶠ τ : UpperHalfPlane in 𝓝[≠] τ0, PkgI1.jDen (PkgI1.Omega (τ : ℂ)) ≠ 0 := by
  have h := jDenO_eventually_ne (z := (τ0 : ℂ)) τ0.im_pos
  rw [← map_coe_punctured] at h
  exact Filter.eventually_map.1 h

open Filter Topology in
theorem value_infty_of_tendsto {f : UpperHalfPlane → OnePoint ℂ} (hc : Continuous f) {h : ℂ → ℂ}
    (τ0 : UpperHalfPlane) (hev : ∀ᶠ τ : UpperHalfPlane in 𝓝[≠] τ0, f τ = ((h τ : ℂ) : OnePoint ℂ))
    (ht : Tendsto h (𝓝[≠] (τ0 : ℂ)) (Bornology.cobounded ℂ)) : f τ0 = OnePoint.infty := by
  have h1 : Tendsto f (𝓝[≠] τ0) (𝓝 (f τ0)) := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hcoe : Tendsto (fun z : ℂ => (z : OnePoint ℂ)) (Bornology.cobounded ℂ) (𝓝 OnePoint.infty) := by
    rw [Metric.cobounded_eq_cocompact, ← Filter.coclosedCompact_eq_cocompact]
    exact OnePoint.tendsto_coe_infty
  have hh : Tendsto (fun τ : UpperHalfPlane => h τ) (𝓝[≠] τ0) (Bornology.cobounded ℂ) :=
    ht.comp (le_of_eq (map_coe_punctured τ0))
  have h2 : Tendsto f (𝓝[≠] τ0) (𝓝 OnePoint.infty) :=
    (hcoe.comp hh).congr' (hev.mono fun τ hτ => hτ.symm)
  exact tendsto_nhds_unique h1 h2

open Filter Topology in
theorem value_of_eventually {f : UpperHalfPlane → OnePoint ℂ} (hc : Continuous f) (τ0 : UpperHalfPlane)
    (v : OnePoint ℂ) (hev : ∀ᶠ τ : UpperHalfPlane in 𝓝[≠] τ0, f τ = v) : f τ0 = v := by
  have h1 : Tendsto f (𝓝[≠] τ0) (𝓝 (f τ0)) := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[≠] τ0) (𝓝 v) := tendsto_const_nhds.congr' (hev.mono fun τ hτ => hτ.symm)
  exact tendsto_nhds_unique h1 h2

end HDec.LeafQCheck.HM

#print axioms HDec.LeafQCheck.HM.qmHauptmodul_of_base
#print axioms HDec.LeafQCheck.HM.qmHauptmodul_of_base2
