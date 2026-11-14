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

end HDec.LeafQCheck.HM
