import ZInQKernel.Contrib.TYZGenus.ShimuraMain
import ZInQKernel.Contrib.GZTheta.Eta

/-!
# tyz-cm: `Γ₀(32)`-invariance of x0-32's `y` and `(x − 2)²` (proved), and of `x` from the curve
# equation

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

* **Closed form of the `η²` multiplier** (`etaSqExp_closed`): gz-theta's Euclidean exponent
  `etaSqExp` (`η(γz)² = ζ^{φ(γ)}(cz + d)η(z)²`, `ζ = e^{πi/6}`, `GZTheta/Eta.lean`) satisfies
  `φ(γ) ≡ (a − 2d)c − bd(c² − 1) + 3d − 3 (mod 12)` for `d` odd and
  `φ(γ) ≡ (a + d)c − bd(c² − 1) − 3c (mod 12)` for `c` odd (Petersson's formula, squared). Proof:
  induction along the Euclidean recursion; each step is a polynomial congruence mod 12, checked in
  `ZMod 4` and `ZMod 3` by `decide`.
* For `γ ∈ Γ₀(32)` and `δ ∣ 32`: `η(δγτ)² = ζ^{X_δ}(cτ + d)η(δτ)²`; the exponents combine to
  `−36bd` for `y` and to `12(2k(a − 2d) − bd(64k² + 4))` for `(x − 2)²` (`c = 32k`), so
  `y∘γ = y` (`yC_gamma0`) and `(x∘γ − 2)² = (x − 2)²` (`xC_sub_two_sq_gamma0`), unconditionally.
* With x0-32's leaf `X0.EtaModelEquation` (`y² = x³ + 4x`): `x∘γ − 2 = ±(x − 2)` on the connected
  `ℍ`, and the sign `−1` would force `2x³ − 12x² + 56x − 80 = 0` on `ℍ`, contradicting
  `|x(it)| → ∞`. Hence `etaModelInvariant_of_equation : X0.EtaModelEquation → X0.EtaModelInvariant`
  and the CM leaf from `CMValueRingClass` and `X0.EtaModelEquation`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open Complex Filter Topology
open ZInQ.GZTheta (etaSqExp zeta12 zeta12_ne_zero zeta12_zpow_emod eta_sq_mobius
  mobius_denom_ne_zero mobius_im_pos)

/-! ## The closed form of `etaSqExp` modulo 12 -/

/-- `X(a, b, c, d) = (a − 2d)c − bd(c² − 1) + 3d − 3`. -/
def XfR {R : Type*} [CommRing R] (a b c d : R) : R :=
  (a - 2 * d) * c - b * d * (c ^ 2 - 1) + 3 * d - 3

/-- `Y(a, b, c, d) = (a + d)c − bd(c² − 1) − 3c`. -/
def YfR {R : Type*} [CommRing R] (a b c d : R) : R :=
  (a + d) * c - b * d * (c ^ 2 - 1) - 3 * c

theorem XfR_intCast (n : ℕ) (a b c d : ℤ) :
    ((XfR a b c d : ℤ) : ZMod n) = XfR (a : ZMod n) (b : ZMod n) (c : ZMod n) (d : ZMod n) := by
  simp only [XfR]; push_cast; ring

theorem YfR_intCast (n : ℕ) (a b c d : ℤ) :
    ((YfR a b c d : ℤ) : ZMod n) = YfR (a : ZMod n) (b : ZMod n) (c : ZMod n) (d : ZMod n) := by
  simp only [YfR]; push_cast; ring

theorem dvd12_of {P : ℤ} (h4 : ((P : ℤ) : ZMod 4) = 0) (h3 : ((P : ℤ) : ZMod 3) = 0) :
    (12 : ℤ) ∣ P := by
  have a := (ZMod.intCast_zmod_eq_zero_iff_dvd P 4).1 h4
  have b := (ZMod.intCast_zmod_eq_zero_iff_dvd P 3).1 h3
  omega

theorem odd_cast4 {d : ℤ} (hd : d % 2 = 1) : (d : ZMod 4) = 1 ∨ (d : ZMod 4) = 3 := by
  have h : d % 4 = 1 ∨ d % 4 = 3 := by omega
  rw [← ZMod.intCast_mod d 4]
  rcases h with h | h <;> rw [show ((4 : ℕ) : ℤ) = 4 by norm_num, h]
  · left; rfl
  · right; rfl

theorem cast_det {n : ℕ} {c d r b : ℤ} (h : d * r - c * b = 1) :
    (d : ZMod n) * r - c * b = 1 := by
  have := congrArg (fun x : ℤ => (x : ZMod n)) h
  push_cast at this
  exact this

section Steps
variable (c d q r b : ℤ)

theorem step_dX (h : d * r - c * b = 1) (hd : d % 2 = 1) (hb : b % 2 = 1) :
    (12 : ℤ) ∣ XfR (c * q + r) (b + q * d) c d - (q - 3 + XfR c d (-r) (-b)) := by
  have k4 : ∀ c d q r b : ZMod 4, d * r - c * b = 1 → (d = 1 ∨ d = 3) → (b = 1 ∨ b = 3) →
      XfR (c * q + r) (b + q * d) c d - (q - 3 + XfR c d (-r) (-b)) = 0 := by decide
  have k3 : ∀ c d q r b : ZMod 3, d * r - c * b = 1 →
      XfR (c * q + r) (b + q * d) c d - (q - 3 + XfR c d (-r) (-b)) = 0 := by decide
  refine dvd12_of ?_ ?_
  · push_cast [XfR_intCast]; exact k4 _ _ _ _ _ (cast_det h) (odd_cast4 hd) (odd_cast4 hb)
  · push_cast [XfR_intCast]; exact k3 _ _ _ _ _ (cast_det h)

theorem step_dY (h : d * r - c * b = 1) (hd : d % 2 = 1) (hr : r % 2 = 1) :
    (12 : ℤ) ∣ XfR (c * q + r) (b + q * d) c d - (q - 3 + YfR c d (-r) (-b)) := by
  have k4 : ∀ c d q r b : ZMod 4, d * r - c * b = 1 → (d = 1 ∨ d = 3) → (r = 1 ∨ r = 3) →
      XfR (c * q + r) (b + q * d) c d - (q - 3 + YfR c d (-r) (-b)) = 0 := by decide
  have k3 : ∀ c d q r b : ZMod 3, d * r - c * b = 1 →
      XfR (c * q + r) (b + q * d) c d - (q - 3 + YfR c d (-r) (-b)) = 0 := by decide
  refine dvd12_of ?_ ?_
  · push_cast [XfR_intCast, YfR_intCast]
    exact k4 _ _ _ _ _ (cast_det h) (odd_cast4 hd) (odd_cast4 hr)
  · push_cast [XfR_intCast, YfR_intCast]; exact k3 _ _ _ _ _ (cast_det h)

theorem step_cX (h : d * r - c * b = 1) (hc : c % 2 = 1) (hb : b % 2 = 1) :
    (12 : ℤ) ∣ YfR (c * q + r) (b + q * d) c d - (q - 3 + XfR c d (-r) (-b)) := by
  have k4 : ∀ c d q r b : ZMod 4, d * r - c * b = 1 → (c = 1 ∨ c = 3) → (b = 1 ∨ b = 3) →
      YfR (c * q + r) (b + q * d) c d - (q - 3 + XfR c d (-r) (-b)) = 0 := by decide
  have k3 : ∀ c d q r b : ZMod 3, d * r - c * b = 1 →
      YfR (c * q + r) (b + q * d) c d - (q - 3 + XfR c d (-r) (-b)) = 0 := by decide
  refine dvd12_of ?_ ?_
  · push_cast [XfR_intCast, YfR_intCast]
    exact k4 _ _ _ _ _ (cast_det h) (odd_cast4 hc) (odd_cast4 hb)
  · push_cast [XfR_intCast, YfR_intCast]; exact k3 _ _ _ _ _ (cast_det h)

theorem step_cY (h : d * r - c * b = 1) (hc : c % 2 = 1) (hr : r % 2 = 1) :
    (12 : ℤ) ∣ YfR (c * q + r) (b + q * d) c d - (q - 3 + YfR c d (-r) (-b)) := by
  have k4 : ∀ c d q r b : ZMod 4, d * r - c * b = 1 → (c = 1 ∨ c = 3) → (r = 1 ∨ r = 3) →
      YfR (c * q + r) (b + q * d) c d - (q - 3 + YfR c d (-r) (-b)) = 0 := by decide
  have k3 : ∀ c d q r b : ZMod 3, d * r - c * b = 1 →
      YfR (c * q + r) (b + q * d) c d - (q - 3 + YfR c d (-r) (-b)) = 0 := by decide
  refine dvd12_of ?_ ?_
  · push_cast [YfR_intCast]; exact k4 _ _ _ _ _ (cast_det h) (odd_cast4 hc) (odd_cast4 hr)
  · push_cast [YfR_intCast]; exact k3 _ _ _ _ _ (cast_det h)

end Steps

/-- Base case `c = 0`. -/
theorem etaSqExp_base (a b d : ℤ) (h : a * d - b * 0 = 1) :
    (12 : ℤ) ∣ XfR a b 0 d - (if a = 1 then b else 6 - b) := by
  have had : a * d = 1 := by simpa using h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [XfR]
  · rw [if_neg (by decide)]
    exact ⟨-1, by simp [XfR]; ring⟩

/-- **Closed form of gz-theta's `η²` exponent modulo 12** (Petersson's formula, squared). -/
theorem etaSqExp_closed : ∀ (fuel : ℕ) (a b c d : ℤ), c.natAbs ≤ fuel → a * d - b * c = 1 →
    (d % 2 = 1 → (12 : ℤ) ∣ XfR a b c d - etaSqExp fuel a b c d) ∧
    (c % 2 = 1 → (12 : ℤ) ∣ YfR a b c d - etaSqExp fuel a b c d) := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b c d hc h
    have hc0 : c = 0 := by omega
    subst hc0
    refine ⟨fun _ => ?_, fun h' => by simp at h'⟩
    simpa [etaSqExp] using etaSqExp_base a b d h
  | succ n ih =>
    intro a b c d hc h
    by_cases hc0 : c = 0
    · subst hc0
      refine ⟨fun _ => ?_, fun h' => by simp at h'⟩
      simpa [etaSqExp] using etaSqExp_base a b d h
    simp only [etaSqExp, if_neg hc0]
    set q := a / c with hq
    set r := a % c with hr
    set b' := b - q * d with hb'
    have hqr : c * q + r = a := Int.mul_ediv_add_emod a c
    have hr0 : 0 ≤ r := Int.emod_nonneg a hc0
    have hrc : r < (c.natAbs : ℤ) := Int.emod_lt a hc0
    have hdet3 : c * -b' - d * -r = 1 := by
      rw [hb']; rw [← hqr] at h; linear_combination h
    have hdet' : d * r - c * b' = 1 := by linear_combination hdet3
    have hc3 : (-r).natAbs ≤ n := by
      rw [Int.natAbs_neg]
      have h1 : (r.natAbs : ℤ) = r := Int.natAbs_of_nonneg hr0
      have h2 : (c.natAbs : ℤ) ≤ (n : ℤ) + 1 := by exact_mod_cast hc
      omega
    obtain ⟨ihX, ihY⟩ := ih c d (-r) (-b') hc3 hdet3
    have hb : b = b' + q * d := by rw [hb']; ring
    have hpar : b' % 2 = 1 ∨ r % 2 = 1 := by
      by_contra hne
      push_neg at hne
      have h1 : b' % 2 = 0 := by omega
      have h2 : r % 2 = 0 := by omega
      obtain ⟨s, hs⟩ := Int.dvd_of_emod_eq_zero h1
      obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h2
      rw [hs, ht] at hdet'
      have h3 : (2 : ℤ) * (d * t - c * s) = 1 := by linear_combination hdet'
      omega
    have e1 : XfR a b c d = XfR (c * q + r) (b' + q * d) c d := by rw [hqr, ← hb]
    have e2 : YfR a b c d = YfR (c * q + r) (b' + q * d) c d := by rw [hqr, ← hb]
    refine ⟨fun hd => ?_, fun hcodd => ?_⟩
    · rw [e1]
      rcases hpar with hb1 | hr1
      · have h3 := ihX (by omega)
        have h4 := step_dX c d q r b' hdet' hd hb1
        have := dvd_add h4 h3
        convert this using 1; ring
      · have h3 := ihY (by omega)
        have h4 := step_dY c d q r b' hdet' hd hr1
        have := dvd_add h4 h3
        convert this using 1; ring
    · rw [e2]
      rcases hpar with hb1 | hr1
      · have h3 := ihX (by omega)
        have h4 := step_cX c d q r b' hdet' hcodd hb1
        have := dvd_add h4 h3
        convert this using 1; ring
      · have h3 := ihY (by omega)
        have h4 := step_cY c d q r b' hdet' hcodd hr1
        have := dvd_add h4 h3
        convert this using 1; ring

/-- `ζ^m = ζ^n` when `12 ∣ m − n`. -/
theorem zeta12_zpow_congr {m n : ℤ} (h : (12 : ℤ) ∣ m - n) : zeta12 ^ m = zeta12 ^ n := by
  rw [zeta12_zpow_emod m, zeta12_zpow_emod n]
  congr 1
  omega

/-! ## `η(δγτ)²` for `γ ∈ Γ₀(32)` -/

theorem etaD_sq_smul {δ : ℕ} (hδ : 0 < δ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {k : ℤ}
    (hk : γ 1 0 = δ * k) (hd : γ 1 1 % 2 = 1) (τ : UpperHalfPlane) :
    X0.etaD δ ((γ • τ : UpperHalfPlane) : ℂ) ^ 2 =
      zeta12 ^ (XfR (γ 0 0) (δ * γ 0 1) k (γ 1 1)) * ((γ 1 0 : ℂ) * τ + γ 1 1) *
        X0.etaD δ τ ^ 2 := by
  have hdet0 : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
  have hdet : γ 0 0 * γ 1 1 - (δ * γ 0 1) * k = 1 := by
    have h' := hdet0; rw [hk] at h'; linear_combination h'
  have hz : 0 < ((δ : ℂ) * τ).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    have := τ.im_pos
    have : (0 : ℝ) < δ := by exact_mod_cast hδ
    show 0 < (δ : ℝ) * τ.im
    positivity
  have hm := eta_sq_mobius k.natAbs (γ 0 0) (δ * γ 0 1) k (γ 1 1) le_rfl hdet ((δ : ℂ) * τ) hz
  have hkC : (γ 1 0 : ℂ) = δ * k := by exact_mod_cast hk
  have hden := mobius_denom_ne_zero hdet0 τ.im_pos
  have hcoe : ((γ • τ : UpperHalfPlane) : ℂ) =
      ((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  have harg : (δ : ℂ) * ((γ • τ : UpperHalfPlane) : ℂ) =
      ((γ 0 0 : ℂ) * (δ * τ) + ((δ * γ 0 1 : ℤ) : ℂ)) / ((k : ℂ) * (δ * τ) + γ 1 1) := by
    rw [hcoe]
    have hden' : (k : ℂ) * (δ * τ) + γ 1 1 = (γ 1 0 : ℂ) * τ + γ 1 1 := by rw [hkC]; ring
    rw [hden']
    push_cast
    field_simp
  have hfac : (k : ℂ) * (δ * τ) + γ 1 1 = (γ 1 0 : ℂ) * τ + γ 1 1 := by rw [hkC]; ring
  have hexp : zeta12 ^ (etaSqExp k.natAbs (γ 0 0) (δ * γ 0 1) k (γ 1 1)) =
      zeta12 ^ (XfR (γ 0 0) (δ * γ 0 1) k (γ 1 1)) := by
    apply zeta12_zpow_congr
    have := (etaSqExp_closed k.natAbs (γ 0 0) (δ * γ 0 1) k (γ 1 1) le_rfl hdet).1 hd
    rw [← dvd_neg]; convert this using 1; ring
  unfold X0.etaD
  rw [harg, hm, hexp, hfac]

/-- For `γ ∈ Γ₀(32)`: `c = 32k` and `d` odd. -/
theorem gamma0_32_data {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 32) :
    ∃ k : ℤ, γ 1 0 = 32 * k ∧ γ 1 1 % 2 = 1 := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) 32).1 hγ
  refine ⟨k, by exact_mod_cast hk, ?_⟩
  have hdet0 : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
  rw [hk] at hdet0
  have hodd : Odd (γ 0 0 * γ 1 1) := ⟨16 * (γ 0 1 * k), by push_cast at hdet0; linear_combination hdet0⟩
  have := (Int.odd_mul.1 hodd).2
  exact Int.odd_iff.1 this

/-! ## `y` and `(x − 2)²` are `Γ₀(32)`-invariant -/

/-- **`y` is `Γ₀(32)`-invariant** (unconditional). -/
theorem yC_gamma0 (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 32) (τ : UpperHalfPlane) :
    X0.yC ((γ • τ : UpperHalfPlane) : ℂ) = X0.yC τ := by
  obtain ⟨k, hk, hd⟩ := gamma0_32_data hγ
  set a := γ 0 0
  set b := γ 0 1
  set d := γ 1 1
  set L : ℂ := (γ 1 0 : ℂ) * τ + d
  have hL : L ≠ 0 := by
    have hdet0 : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
    exact mobius_denom_ne_zero hdet0 τ.im_pos
  have h4 := etaD_sq_smul (δ := 4) (by norm_num) γ (k := 8 * k) (by rw [hk]; push_cast; ring) hd τ
  have h8 := etaD_sq_smul (δ := 8) (by norm_num) γ (k := 4 * k) (by rw [hk]; push_cast; ring) hd τ
  have h16 := etaD_sq_smul (δ := 16) (by norm_num) γ (k := 2 * k) (by rw [hk]; push_cast; ring) hd τ
  have h32 := etaD_sq_smul (δ := 32) (by norm_num) γ (k := k) (by rw [hk]; push_cast; ring) hd τ
  set A4 := zeta12 ^ (XfR a ((4 : ℕ) * b) (8 * k) d)
  set A8 := zeta12 ^ (XfR a ((8 : ℕ) * b) (4 * k) d)
  set A16 := zeta12 ^ (XfR a ((16 : ℕ) * b) (2 * k) d)
  set A32 := zeta12 ^ (XfR a ((32 : ℕ) * b) k d)
  have hA4 : A4 ≠ 0 := zpow_ne_zero _ zeta12_ne_zero
  have hA32 : A32 ≠ 0 := zpow_ne_zero _ zeta12_ne_zero
  have hratio : A8 ^ 2 * A16 / (A4 * A32 ^ 2) = 1 := by
    rw [div_eq_one_iff_eq (mul_ne_zero hA4 (pow_ne_zero _ hA32))]
    simp only [A4, A8, A16, A32, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ zeta12_ne_zero]
    apply zeta12_zpow_congr
    exact ⟨-3 * b * d, by simp only [XfR]; push_cast; ring⟩
  set E4 := X0.etaD 4 τ ^ 2
  set E8 := X0.etaD 8 τ ^ 2
  set E16 := X0.etaD 16 τ ^ 2
  set E32 := X0.etaD 32 τ ^ 2
  have hE4 : E4 ≠ 0 := pow_ne_zero _ (X0.etaD_ne_zero (by norm_num) τ)
  have hE32 : E32 ≠ 0 := pow_ne_zero _ (X0.etaD_ne_zero (by norm_num) τ)
  have hy : ∀ z : ℂ, X0.yC z = -((X0.etaD 8 z ^ 2) ^ 2 * X0.etaD 16 z ^ 2 /
      (X0.etaD 4 z ^ 2 * (X0.etaD 32 z ^ 2) ^ 2)) := fun z => by unfold X0.yC; ring
  rw [hy, hy, h4, h8, h16, h32]
  calc -((A8 * L * E8) ^ 2 * (A16 * L * E16) / ((A4 * L * E4) * (A32 * L * E32) ^ 2))
      = -((A8 ^ 2 * A16 / (A4 * A32 ^ 2)) * (E8 ^ 2 * E16 / (E4 * E32 ^ 2))) := by
        field_simp
    _ = -(E8 ^ 2 * E16 / (E4 * E32 ^ 2)) := by rw [hratio, one_mul]

/-- **`(x − 2)²` is `Γ₀(32)`-invariant** (unconditional). -/
theorem xC_sub_two_sq_gamma0 (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 32) (τ : UpperHalfPlane) :
    (X0.xC ((γ • τ : UpperHalfPlane) : ℂ) - 2) ^ 2 = (X0.xC τ - 2) ^ 2 := by
  obtain ⟨k, hk, hd⟩ := gamma0_32_data hγ
  set a := γ 0 0
  set b := γ 0 1
  set d := γ 1 1
  set L : ℂ := (γ 1 0 : ℂ) * τ + d
  have hL : L ≠ 0 := by
    have hdet0 : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
    exact mobius_denom_ne_zero hdet0 τ.im_pos
  have h2 := etaD_sq_smul (δ := 2) (by norm_num) γ (k := 16 * k) (by rw [hk]; push_cast; ring) hd τ
  have h4 := etaD_sq_smul (δ := 4) (by norm_num) γ (k := 8 * k) (by rw [hk]; push_cast; ring) hd τ
  have h16 := etaD_sq_smul (δ := 16) (by norm_num) γ (k := 2 * k) (by rw [hk]; push_cast; ring) hd τ
  have h32 := etaD_sq_smul (δ := 32) (by norm_num) γ (k := k) (by rw [hk]; push_cast; ring) hd τ
  set A2 := zeta12 ^ (XfR a ((2 : ℕ) * b) (16 * k) d)
  set A4 := zeta12 ^ (XfR a ((4 : ℕ) * b) (8 * k) d)
  set A16 := zeta12 ^ (XfR a ((16 : ℕ) * b) (2 * k) d)
  set A32 := zeta12 ^ (XfR a ((32 : ℕ) * b) k d)
  have hA4 : A4 ≠ 0 := zpow_ne_zero _ zeta12_ne_zero
  have hA32 : A32 ≠ 0 := zpow_ne_zero _ zeta12_ne_zero
  have hratio : A2 ^ 2 * A16 / (A4 * A32 ^ 2) = 1 := by
    rw [div_eq_one_iff_eq (mul_ne_zero hA4 (pow_ne_zero _ hA32))]
    simp only [A2, A4, A16, A32, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ zeta12_ne_zero]
    apply zeta12_zpow_congr
    exact ⟨2 * k * (a - 2 * d) - b * d * (64 * k ^ 2 + 4), by simp only [XfR]; push_cast; ring⟩
  set E2 := X0.etaD 2 τ ^ 2
  set E4 := X0.etaD 4 τ ^ 2
  set E16 := X0.etaD 16 τ ^ 2
  set E32 := X0.etaD 32 τ ^ 2
  have hE4 : E4 ≠ 0 := pow_ne_zero _ (X0.etaD_ne_zero (by norm_num) τ)
  have hE32 : E32 ≠ 0 := pow_ne_zero _ (X0.etaD_ne_zero (by norm_num) τ)
  have hx : ∀ z : ℂ, (X0.xC z - 2) ^ 2 = (X0.etaD 2 z ^ 2) ^ 2 * X0.etaD 16 z ^ 2 /
      (X0.etaD 4 z ^ 2 * (X0.etaD 32 z ^ 2) ^ 2) := fun z => by unfold X0.xC; ring
  rw [hx, hx, h2, h4, h16, h32]
  calc (A2 * L * E2) ^ 2 * (A16 * L * E16) / ((A4 * L * E4) * (A32 * L * E32) ^ 2)
      = (A2 ^ 2 * A16 / (A4 * A32 ^ 2)) * (E2 ^ 2 * E16 / (E4 * E32 ^ 2)) := by
        field_simp
    _ = E2 ^ 2 * E16 / (E4 * E32 ^ 2) := by rw [hratio, one_mul]

/-! ## `x` is `Γ₀(32)`-invariant, given the curve equation -/

theorem xC_sub_two_ne_zero (z : UpperHalfPlane) : X0.xC z - 2 ≠ 0 := by
  have : X0.xC z - 2 = X0.etaD 2 z ^ 2 * X0.etaD 16 z / (X0.etaD 4 z * X0.etaD 32 z ^ 2) := by
    unfold X0.xC; ring
  rw [this]
  have := X0.etaD_ne_zero (d := 2) (by norm_num) z
  have := X0.etaD_ne_zero (d := 4) (by norm_num) z
  have := X0.etaD_ne_zero (d := 16) (by norm_num) z
  have := X0.etaD_ne_zero (d := 32) (by norm_num) z
  positivity

/-- **`x` is `Γ₀(32)`-invariant, given `y² = x³ + 4x`.** -/
theorem xC_gamma0 (hEq : X0.EtaModelEquation) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 32) (τ : UpperHalfPlane) :
    X0.xC ((γ • τ : UpperHalfPlane) : ℂ) = X0.xC τ := by
  set S : Set ℂ := {z : ℂ | 0 < z.im}
  have hS : IsPreconnected S := (convex_halfSpace_im_gt 0).isPreconnected
  have hdet0 : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
  set M : ℂ → ℂ := fun z => ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)
  have hcoe : ∀ τ' : UpperHalfPlane, ((γ • τ' : UpperHalfPlane) : ℂ) = M τ' := by
    intro τ'
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [M]
  set f : ℂ → ℂ := fun z => X0.xC (M z) - 2
  set g : ℂ → ℂ := fun z => X0.xC z - 2
  have hg : ContinuousOn g S := by
    intro z hz
    exact ((X0.differentiableAt_xC ⟨z, hz⟩).continuousAt.sub continuousAt_const).continuousWithinAt
  have hf : ContinuousOn f S := by
    intro z hz
    have hMc : ContinuousAt M z := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      exact mobius_denom_ne_zero hdet0 hz
    have hMz : 0 < (M z).im := mobius_im_pos hdet0 hz
    have hx : ContinuousAt X0.xC (M z) := (X0.differentiableAt_xC ⟨M z, hMz⟩).continuousAt
    exact ((hx.comp hMc).sub continuousAt_const).continuousWithinAt
  have hsq : Set.EqOn (f ^ 2) (g ^ 2) S := by
    intro z hz
    have := xC_sub_two_sq_gamma0 γ hγ ⟨z, hz⟩
    rw [hcoe] at this
    simpa [f, g] using this
  have hne : ∀ {z : ℂ}, z ∈ S → g z ≠ 0 := fun {z} hz => xC_sub_two_ne_zero ⟨z, hz⟩
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg hsq hne with h | h
  · have := h τ.im_pos
    simp only [f, g] at this
    rw [hcoe]
    linear_combination this
  · exfalso
    -- `x∘γ = 4 − x` on `ℍ` contradicts the curve equation at a point with `|x| ≥ 10`
    have hrel : ∀ τ' : UpperHalfPlane,
        2 * X0.xC τ' ^ 3 - 12 * X0.xC τ' ^ 2 + 56 * X0.xC τ' - 80 = 0 := by
      intro τ'
      have h1 := h τ'.im_pos
      simp only [f, g, Pi.neg_apply] at h1
      have hxg : X0.xC ((γ • τ' : UpperHalfPlane) : ℂ) = 4 - X0.xC τ' := by
        rw [hcoe]; linear_combination h1
      have e1 := hEq (γ • τ')
      have e2 := hEq τ'
      rw [yC_gamma0 γ hγ τ', hxg] at e1
      linear_combination e1 - e2
    have hev := (X0.tendsto_norm_xC_atTop.eventually_ge_atTop 10).and
      (eventually_ge_atTop (1 : ℝ))
    obtain ⟨t, ht, ht1⟩ := hev.exists
    have him : 0 < ((t : ℂ) * I).im := by simp; linarith
    have hr := hrel ⟨(t : ℂ) * I, him⟩
    set X := X0.xC ((t : ℂ) * I)
    change 2 * X ^ 3 - 12 * X ^ 2 + 56 * X - 80 = 0 at hr
    have hX : 10 ≤ ‖X‖ := ht
    have h3 : ‖2 * X ^ 3‖ ≤ ‖12 * X ^ 2‖ + ‖56 * X‖ + 80 := by
      have : 2 * X ^ 3 = 12 * X ^ 2 - 56 * X + 80 := by linear_combination hr
      rw [this]
      calc ‖12 * X ^ 2 - 56 * X + 80‖ ≤ ‖12 * X ^ 2 - 56 * X‖ + ‖(80 : ℂ)‖ := norm_add_le _ _
        _ ≤ ‖12 * X ^ 2‖ + ‖56 * X‖ + ‖(80 : ℂ)‖ := by gcongr; exact norm_sub_le _ _
        _ = ‖12 * X ^ 2‖ + ‖56 * X‖ + 80 := by norm_num
    simp only [norm_mul, norm_pow, Complex.norm_ofNat] at h3
    nlinarith [sq_nonneg ‖X‖]

/-- **`X0.EtaModelInvariant` from `X0.EtaModelEquation`.** -/
theorem etaModelInvariant_of_equation (hEq : X0.EtaModelEquation) : X0.EtaModelInvariant :=
  fun γ hγ τ => ⟨xC_gamma0 hEq γ hγ τ, yC_gamma0 γ hγ τ⟩

/-- **The CM leaf from `CMValueRingClass` and x0-32's curve-equation leaf.** -/
theorem cmFieldOfDefinition_of_cmValue_eq (hV : CMValueRingClass) (hEq : X0.EtaModelEquation) :
    ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition RingClass.ringClassFieldD :=
  cmFieldOfDefinition_of_cmValue hV (etaModelInvariant_of_equation hEq)

end ZInQ.Contrib.TYZGenus.Shimura
