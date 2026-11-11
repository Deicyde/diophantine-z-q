import ZInQKernel.Hypotheses.CertifiedRank
import ZInQKernel.Model.Field.ShortWeierstrass

/-!
# Proposition 0: the 2-coverings of `C_d` and the 2-Selmer group

`docs/research/nt-prop0.md` §1. For a field `K` and `d, a, b ∈ K`, the 2-covering of
`C_d : y² = x³ − d²x` attached to `(a, b)` is

```
D_{a,b} :  a z₁² − b z₂² = d w²,   a z₁² − ab z₃² = −d w²    in ℙ³.
```

* `Loc K d a b` is its solubility in "x-form": `a, b` are squares, or some `x ∈ K` makes `x/a`,
  `(x − d)/b` and `(x + d)/(ab)` squares (zero allowed). `cov_iff_loc` shows that this is
  `D_{a,b}(K) ≠ ∅`, and `loc_iff_kummer` (Lemma 1.2) that it says `(a, b)` lies in the image of
  the Kummer map `δ_K : C_d(K) → (K*/K*²)²` (`kummer`).
* `loc_congr_sq` (Inv) and `loc_torsion` (Tor) are the two remarks of §2 used at every place.
* `Sel2 d` is the set of pairs of squarefree integers whose covering is soluble over `ℝ` and every
  `ℚ_p`: the 2-Selmer group of `C_d` (§1.3).
* `CertifiedRankSel` is hypothesis CR₃ in the literature's form (§1.4), and
  `certifiedRank_of_sel` derives `ZInQ.CertifiedRank` from it and Proposition 0
  (`Prop0Statement`, §2.7).
-/

namespace ZInQ.RouteK.Selmer

open WeierstrassCurve WeierstrassCurve.Affine

section Field

variable {K : Type*} [Field K]

/-- `u ≡ v` in `K*/K*²`, written as `u = v s²` with `s ≠ 0`. -/
def SqEq (u v : K) : Prop := ∃ s : K, s ≠ 0 ∧ u = v * s ^ 2

theorem SqEq.refl (u : K) : SqEq u u := ⟨1, one_ne_zero, by ring⟩

theorem SqEq.symm {u v : K} (h : SqEq u v) : SqEq v u := by
  obtain ⟨s, hs, rfl⟩ := h
  exact ⟨s⁻¹, inv_ne_zero hs, by field_simp⟩

theorem SqEq.trans {u v w : K} (h₁ : SqEq u v) (h₂ : SqEq v w) : SqEq u w := by
  obtain ⟨s, hs, rfl⟩ := h₁
  obtain ⟨t, ht, rfl⟩ := h₂
  exact ⟨t * s, mul_ne_zero ht hs, by ring⟩

theorem SqEq.mul {u v u' v' : K} (h : SqEq u v) (h' : SqEq u' v') : SqEq (u * u') (v * v') := by
  obtain ⟨s, hs, rfl⟩ := h
  obtain ⟨t, ht, rfl⟩ := h'
  exact ⟨s * t, mul_ne_zero hs ht, by ring⟩

/-- `u ≡ v` makes `u v` a square. -/
theorem SqEq.isSquare_mul {u v : K} (h : SqEq u v) : IsSquare (u * v) := by
  obtain ⟨s, -, rfl⟩ := h
  exact ⟨v * s, by ring⟩

theorem SqEq.ne_zero {u v : K} (h : SqEq u v) (hv : v ≠ 0) : u ≠ 0 := by
  obtain ⟨s, hs, rfl⟩ := h
  exact mul_ne_zero hv (pow_ne_zero 2 hs)

/-- For `v ≠ 0`, `u ≡ v` iff `u ≠ 0` and `u v` is a square. -/
theorem sqEq_iff_isSquare_mul {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) :
    SqEq u v ↔ IsSquare (u * v) := by
  refine ⟨SqEq.isSquare_mul, fun ⟨r, hr⟩ => ⟨r / v, ?_, ?_⟩⟩
  · rintro h
    rw [div_eq_zero_iff, or_iff_left hv] at h
    subst h
    exact mul_ne_zero hu hv (by rw [hr, mul_zero])
  · rw [div_pow, sq r, ← hr]
    field_simp

theorem isSquare_mul_sq_iff {u c : K} (hc : c ≠ 0) : IsSquare (u * c ^ 2) ↔ IsSquare u := by
  refine ⟨fun h => ?_, fun h => h.mul (IsSquare.sq c)⟩
  have := h.mul (IsSquare.sq c⁻¹)
  rwa [mul_assoc, ← mul_pow, mul_inv_cancel₀ hc, one_pow, mul_one] at this

theorem isSquare_div_sq_iff {u c : K} (hc : c ≠ 0) : IsSquare (u / c ^ 2) ↔ IsSquare u := by
  rw [div_eq_mul_inv, ← inv_pow, isSquare_mul_sq_iff (inv_ne_zero hc)]

/-- `u ≡ v` transports squareness. -/
theorem SqEq.isSquare_iff {u v : K} (h : SqEq u v) : IsSquare u ↔ IsSquare v := by
  obtain ⟨s, hs, rfl⟩ := h
  exact isSquare_mul_sq_iff hs

/-- The 2-covering `D_{a,b}` of `C_d` in "x-form" (nt-prop0 §1.1): `a` and `b` are squares, or
there is `x ∈ K` with `x/a`, `(x − d)/b` and `(x + d)/(ab)` squares (zero allowed). For `a, b ≠ 0`
this is `D_{a,b}(K) ≠ ∅` (`cov_iff_loc`). -/
def Loc (K : Type*) [Field K] (d a b : K) : Prop :=
  (IsSquare a ∧ IsSquare b) ∨
    ∃ x : K, IsSquare (x / a) ∧ IsSquare ((x - d) / b) ∧ IsSquare ((x + d) / (a * b))

/-- **(Inv)** `Loc` depends only on the square classes of `a` and `b`, with the same `x`. -/
theorem loc_mul_sq_iff {d a b s t : K} (hs : s ≠ 0) (ht : t ≠ 0) :
    Loc K d (a * s ^ 2) (b * t ^ 2) ↔ Loc K d a b := by
  have h1 : ∀ x : K, x / (a * s ^ 2) = x / a / s ^ 2 := fun x => by rw [div_div]
  have h2 : ∀ x : K, x / (b * t ^ 2) = x / b / t ^ 2 := fun x => by rw [div_div]
  have h3 : ∀ x : K, x / (a * s ^ 2 * (b * t ^ 2)) = x / (a * b) / (s * t) ^ 2 := fun x => by
    rw [div_div]; ring_nf
  simp only [Loc, isSquare_mul_sq_iff hs, isSquare_mul_sq_iff ht, h1, h2, h3,
    isSquare_div_sq_iff hs, isSquare_div_sq_iff ht, isSquare_div_sq_iff (mul_ne_zero hs ht)]

/-- **(Inv)**, in the form `a ≡ a'`, `b ≡ b'`. -/
theorem loc_congr_sq {d a b a' b' : K} (ha : SqEq a a') (hb : SqEq b b') :
    Loc K d a b ↔ Loc K d a' b' := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact loc_mul_sq_iff hs ht

/-- **(Tor)** A witness `x` of the second alternative of `Loc` is either one of `0, d, −d`, and then
`(a, b)` is the torsion class `(−1, −d)`, `(d, 2)` or `(−d, −2d)`, or `x, x ∓ d` are nonzero with
`x ≡ a`, `x − d ≡ b`, `x + d ≡ ab`, and `x(x − d)(x + d)` is a square. -/
theorem loc_torsion {d a b x : K} (h2 : (2 : K) ≠ 0) (hd : d ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : IsSquare (x / a)) (h₂ : IsSquare ((x - d) / b)) (h₃ : IsSquare ((x + d) / (a * b))) :
    (x = 0 ∧ SqEq a (-1) ∧ SqEq b (-d)) ∨ (x = d ∧ SqEq a d ∧ SqEq b 2) ∨
      (x = -d ∧ SqEq a (-d) ∧ SqEq b (-2 * d)) ∨
      (x ≠ 0 ∧ x - d ≠ 0 ∧ x + d ≠ 0 ∧ SqEq x a ∧ SqEq (x - d) b ∧ SqEq (x + d) (a * b) ∧
        IsSquare (x * (x - d) * (x + d))) := by
  obtain ⟨r₁, e₁⟩ := h₁
  obtain ⟨r₂, e₂⟩ := h₂
  obtain ⟨r₃, e₃⟩ := h₃
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have f₁ : x = a * r₁ ^ 2 := by rw [sq, ← e₁]; field_simp
  have f₂ : x - d = b * r₂ ^ 2 := by rw [sq, ← e₂]; field_simp
  have f₃ : x + d = a * b * r₃ ^ 2 := by rw [sq, ← e₃]; field_simp
  have nz : ∀ {u c r : K}, u ≠ 0 → u = c * r ^ 2 → r ≠ 0 := fun hu h hr => by
    rw [hr] at h; exact hu (by rw [h]; ring)
  by_cases hx0 : x = 0
  · subst hx0
    have hr₂ : r₂ ≠ 0 := nz (neg_ne_zero.mpr hd) (by rw [← f₂]; ring)
    have hr₃ : r₃ ≠ 0 := nz hd (by rw [← f₃]; ring)
    have g : a * r₃ ^ 2 + r₂ ^ 2 = 0 := by
      have : b * (a * r₃ ^ 2 + r₂ ^ 2) = 0 := by linear_combination -f₂ - f₃
      exact (mul_eq_zero.mp this).resolve_left hb
    refine Or.inl ⟨rfl, ⟨r₂ / r₃, div_ne_zero hr₂ hr₃, ?_⟩, ⟨r₂⁻¹, inv_ne_zero hr₂, ?_⟩⟩
    · field_simp
      linear_combination g
    · field_simp
      linear_combination -f₂
  by_cases hxd : x - d = 0
  · have hx : x = d := sub_eq_zero.mp hxd
    subst hx
    have hr₁ : r₁ ≠ 0 := nz hd f₁
    have hr₃ : r₃ ≠ 0 := nz (mul_ne_zero h2 hd) (by rw [two_mul, f₃])
    have g : b * r₃ ^ 2 - 2 * r₁ ^ 2 = 0 := by
      have : a * (b * r₃ ^ 2 - 2 * r₁ ^ 2) = 0 := by linear_combination 2 * f₁ - f₃
      exact (mul_eq_zero.mp this).resolve_left ha
    refine Or.inr (Or.inl ⟨rfl, ⟨r₁⁻¹, inv_ne_zero hr₁, ?_⟩, ⟨r₁ / r₃, div_ne_zero hr₁ hr₃, ?_⟩⟩)
    · field_simp
      linear_combination -f₁
    · field_simp
      linear_combination g
  by_cases hxd' : x + d = 0
  · have hx : x = -d := eq_neg_of_add_eq_zero_left hxd'
    subst hx
    have hr₁ : r₁ ≠ 0 := nz (neg_ne_zero.mpr hd) f₁
    have hr₂ : r₂ ≠ 0 := nz (by intro h; apply mul_ne_zero h2 hd; linear_combination -h) f₂
    refine Or.inr (Or.inr (Or.inl ⟨rfl, ⟨r₁⁻¹, inv_ne_zero hr₁, ?_⟩,
      ⟨r₂⁻¹, inv_ne_zero hr₂, ?_⟩⟩))
    · field_simp
      linear_combination -f₁
    · field_simp
      linear_combination -f₂
  have hr₁ : r₁ ≠ 0 := nz hx0 f₁
  have hr₂ : r₂ ≠ 0 := nz hxd f₂
  have hr₃ : r₃ ≠ 0 := nz hxd' f₃
  refine Or.inr (Or.inr (Or.inr ⟨hx0, hxd, hxd', ⟨r₁, hr₁, f₁⟩, ⟨r₂, hr₂, f₂⟩, ⟨r₃, hr₃, f₃⟩,
    ⟨a * b * r₁ * r₂ * r₃, ?_⟩⟩))
  rw [show x * (x - d) * (x + d) = (a * r₁ ^ 2) * (b * r₂ ^ 2) * (a * b * r₃ ^ 2) by
    rw [← f₁, ← f₂, ← f₃]]
  ring

/-- Cancellation in `K*/K*²`: from `ab ≡ c` and `b ≡ e` (with `e ≠ 0`) get `a ≡ ce`. -/
theorem sqEq_of_mul_sqEq {a b c e : K} (h₁ : SqEq (a * b) c) (h₂ : SqEq b e) (he : e ≠ 0) :
    SqEq a (c * e) := by
  obtain ⟨s, hs, e₁⟩ := h₁
  obtain ⟨t, ht, rfl⟩ := h₂
  refine ⟨s / (e * t), div_ne_zero hs (mul_ne_zero he ht), ?_⟩
  field_simp
  linear_combination e₁

/-- A square factor can be dropped: `u ≡ v e²`, `e ≠ 0`, gives `u ≡ v`. -/
theorem SqEq.of_mul_sq {u v e : K} (h : SqEq u (v * e ^ 2)) (he : e ≠ 0) : SqEq u v :=
  h.trans ⟨e, he, rfl⟩

/-- **(Inv)** with the torsion witnesses (proof of Lemma 1.2, ⇒): the covering of a torsion class
`(d^i (−1)^j, 2^i (−d)^j)`, `i, j ∈ {0, 1}`, is soluble, hence so is that of any `(a, b)` in such
a class. -/
theorem loc_of_sqEq_torsion {d a b : K} (h2 : (2 : K) ≠ 0) (hd : d ≠ 0) {i j : ℕ} (hi : i < 2)
    (hj : j < 2) (ha : SqEq a (d ^ i * (-1) ^ j)) (hb : SqEq b (2 ^ i * (-d) ^ j)) :
    Loc K d a b := by
  rw [loc_congr_sq ha hb]
  interval_cases i <;> interval_cases j
  · exact Or.inl ⟨⟨1, by ring⟩, ⟨1, by ring⟩⟩
  · refine Or.inr ⟨0, ⟨0, by simp⟩, ⟨1, ?_⟩, ⟨1, ?_⟩⟩ <;> field_simp <;> ring
  · refine Or.inr ⟨d, ⟨1, ?_⟩, ⟨0, by simp⟩, ⟨1, ?_⟩⟩ <;>
      first | (field_simp; done) | (field_simp; ring)
  · refine Or.inr ⟨-d, ⟨1, ?_⟩, ⟨1, ?_⟩, ⟨0, by simp⟩⟩ <;>
      first | (field_simp; done) | (field_simp; ring)

/-! ### The projective covering -/

/-- The 2-covering `D_{a,b} : a z₁² − b z₂² = d w², a z₁² − ab z₃² = −d w²` has a `K`-point. -/
def Cov (K : Type*) [Field K] (d a b : K) : Prop :=
  ∃ z₁ z₂ z₃ w : K, ¬(z₁ = 0 ∧ z₂ = 0 ∧ z₃ = 0 ∧ w = 0) ∧
    a * z₁ ^ 2 - b * z₂ ^ 2 = d * w ^ 2 ∧ a * z₁ ^ 2 - a * b * z₃ ^ 2 = -d * w ^ 2

/-- The x-form of the covering (nt-prop0 §1.1). -/
theorem cov_iff_loc {d a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : Cov K d a b ↔ Loc K d a b := by
  constructor
  · rintro ⟨z₁, z₂, z₃, w, hne, e₁, e₂⟩
    by_cases hw : w = 0
    · subst hw
      have g₁ : a * z₁ ^ 2 = b * z₂ ^ 2 := by linear_combination e₁
      have g₂ : z₁ ^ 2 = b * z₃ ^ 2 := by
        have : a * (z₁ ^ 2 - b * z₃ ^ 2) = 0 := by linear_combination e₂
        linear_combination (mul_eq_zero.mp this).resolve_left ha
      have hz₁ : z₁ ≠ 0 := by
        rintro rfl
        have : z₂ = 0 := by
          have := g₁; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
            mul_zero] at this
          exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp
            ((mul_eq_zero.mp this.symm).resolve_left hb)
        have h3 : z₃ = 0 := by
          have := g₂; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
          exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp
            ((mul_eq_zero.mp this.symm).resolve_left hb)
        exact hne ⟨rfl, this, h3, rfl⟩
      have hz₃ : z₃ ≠ 0 := by
        rintro rfl; apply hz₁; simpa using g₂
      refine Or.inl ⟨⟨z₂ / z₃, ?_⟩, ⟨z₁ / z₃, ?_⟩⟩
      · field_simp
        have : z₁ ^ 2 * (a * z₃ ^ 2 - z₂ ^ 2) = 0 := by
          linear_combination z₃ ^ 2 * g₁ - z₂ ^ 2 * g₂
        linear_combination (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hz₁)
      · field_simp
        linear_combination -g₂
    · refine Or.inr ⟨a * (z₁ / w) ^ 2, ⟨z₁ / w, ?_⟩, ⟨z₂ / w, ?_⟩, ⟨z₃ / w, ?_⟩⟩
      · field_simp
      · field_simp
        linear_combination e₁
      · field_simp
        linear_combination e₂
  · rintro (⟨⟨s, hs⟩, ⟨t, ht⟩⟩ | ⟨x, ⟨r₁, e₁⟩, ⟨r₂, e₂⟩, ⟨r₃, e₃⟩⟩)
    · have hs0 : s ≠ 0 := by rintro rfl; exact ha (by rw [hs, mul_zero])
      have ht0 : t ≠ 0 := by rintro rfl; exact hb (by rw [ht, mul_zero])
      refine ⟨1 / s, 1 / t, 1 / (s * t), 0, fun h => one_div_ne_zero hs0 h.1, ?_, ?_⟩
      · rw [hs, ht]; field_simp; ring
      · rw [hs, ht]; field_simp; ring
    · refine ⟨r₁, r₂, r₃, 1, fun h => one_ne_zero h.2.2.2, ?_, ?_⟩
      · have f₁ : a * r₁ ^ 2 = x := by rw [sq, ← e₁]; field_simp
        have f₂ : b * r₂ ^ 2 = x - d := by rw [sq, ← e₂]; field_simp
        rw [f₁, f₂]; ring
      · have f₁ : a * r₁ ^ 2 = x := by rw [sq, ← e₁]; field_simp
        have f₃ : a * b * r₃ ^ 2 = x + d := by rw [sq, ← e₃]; field_simp
        rw [f₁, f₃]; ring

/-! ### The Kummer map (Lemma 1.2) -/

/-- The Kummer map `δ_K : C_d(K) → K* × K*` of the complete 2-descent on `C_d : y² = x³ − d²x`
(`shortCurve (−d²)`), with values read in `(K*/K*²)²`: `δ(O) = (1, 1)`, `δ(0, 0) = (−1, −d)`,
`δ(d, 0) = (d, 2)`, `δ(−d, 0) = (−d, −2d)` and `δ(x, y) = (x, x − d)` otherwise
(Silverman X.1.4). -/
noncomputable def kummer [DecidableEq K] (d : K) : (shortCurve (-d ^ 2)).toAffine.Point → K × K
  | .zero => (1, 1)
  | .some x _ _ =>
    if x = 0 then (-1, -d) else if x = d then (d, 2) else if x = -d then (-d, -2 * d)
    else (x, x - d)

/-- **Lemma 1.2** (nt-prop0 §1.2). For `a, b ≠ 0`, the covering `D_{a,b}` is soluble over `K` iff
`(a, b)` lies in the image of the Kummer map in `(K*/K*²)²`. -/
theorem loc_iff_kummer [DecidableEq K] {d a b : K} (h2 : (2 : K) ≠ 0) (hd : d ≠ 0) (ha : a ≠ 0)
    (hb : b ≠ 0) :
    Loc K d a b ↔ ∃ P, SqEq a (kummer d P).1 ∧ SqEq b (kummer d P).2 := by
  have hΔ : (shortCurve (-d ^ 2)).Δ ≠ 0 := by
    rw [shortCurve_Δ]
    have : (-64 : K) * (-d ^ 2) ^ 3 = 2 ^ 6 * d ^ 6 := by ring
    rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ hd)
  have hd2 : d ≠ -d := fun h => mul_ne_zero h2 hd (by linear_combination h)
  constructor
  · rintro (⟨⟨s, hs⟩, ⟨t, ht⟩⟩ | ⟨x, h₁, h₂, h₃⟩)
    · have hs0 : s ≠ 0 := by rintro rfl; exact ha (by rw [hs, mul_zero])
      have ht0 : t ≠ 0 := by rintro rfl; exact hb (by rw [ht, mul_zero])
      exact ⟨.zero, ⟨s, hs0, by rw [hs]; simp [kummer]; ring⟩,
        ⟨t, ht0, by rw [ht]; simp [kummer]; ring⟩⟩
    · have hx3 := loc_torsion h2 hd ha hb h₁ h₂ h₃
      obtain ⟨r₁, e₁⟩ := h₁
      obtain ⟨r₂, e₂⟩ := h₂
      obtain ⟨r₃, e₃⟩ := h₃
      have f₁ : x = a * r₁ ^ 2 := by rw [sq, ← e₁]; field_simp
      have f₂ : x - d = b * r₂ ^ 2 := by rw [sq, ← e₂]; field_simp
      have f₃ : x + d = a * b * r₃ ^ 2 := by rw [sq, ← e₃]; field_simp
      have hP : (shortCurve (-d ^ 2)).toAffine.Nonsingular x (a * b * r₁ * r₂ * r₃) := by
        refine (equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp ?_
        rw [shortCurve_equation_iff]
        have : x ^ 3 + -d ^ 2 * x = x * (x - d) * (x + d) := by ring
        rw [this, show x * (x - d) * (x + d) = (a * r₁ ^ 2) * (b * r₂ ^ 2) * (a * b * r₃ ^ 2) by
          rw [← f₁, ← f₂, ← f₃]]
        ring
      refine ⟨.some x _ hP, ?_⟩
      rcases hx3 with ⟨rfl, ha', hb'⟩ | ⟨rfl, ha', hb'⟩ | ⟨rfl, ha', hb'⟩ |
        ⟨hx0, hxd, hxd', ha', hb', -, -⟩
      · simpa [kummer] using ⟨ha', hb'⟩
      · simpa [kummer, hd] using ⟨ha', hb'⟩
      · rw [neg_mul] at hb'
        simpa [kummer, hd, hd2.symm] using ⟨ha', hb'⟩
      · have hx1 : x ≠ d := fun h => hxd (sub_eq_zero.mpr h)
        have hx2 : x ≠ -d := fun h => hxd' (by rw [h]; ring)
        simpa [kummer, hx0, hx1, hx2] using ⟨ha'.symm, hb'.symm⟩
  · rintro ⟨P, ha', hb'⟩
    rw [loc_congr_sq ha' hb']
    rcases P with _ | ⟨x, y, hP⟩
    · exact Or.inl ⟨⟨1, by simp [kummer]⟩, ⟨1, by simp [kummer]⟩⟩
    have heq : y ^ 2 = x * (x - d) * (x + d) := by
      have := (shortCurve_equation_iff _ x y).mp hP.1; rw [this]; ring
    simp only [kummer]
    split_ifs with hx0 hx1 hx2
    · refine Or.inr ⟨0, ⟨0, by simp⟩, ⟨1, ?_⟩, ⟨1, ?_⟩⟩
      · field_simp; ring
      · field_simp; ring
    · refine Or.inr ⟨d, ⟨1, ?_⟩, ⟨0, by simp⟩, ⟨1, ?_⟩⟩
      · field_simp
      · field_simp; ring
    · refine Or.inr ⟨-d, ⟨1, ?_⟩, ⟨1, ?_⟩, ⟨0, by simp⟩⟩
      · field_simp
      · field_simp; ring
    · have h1 : x - d ≠ 0 := sub_ne_zero.mpr hx1
      have h2' : x + d ≠ 0 := fun h => hx2 (eq_neg_of_add_eq_zero_left h)
      refine Or.inr ⟨x, ⟨1, ?_⟩, ⟨1, ?_⟩, ⟨y / (x * (x - d)), ?_⟩⟩
      · field_simp
      · field_simp
      · field_simp
        rw [heq]; ring

end Field

/-! ### The 2-Selmer group and the hypothesis in the literature's form -/

/-- The 2-Selmer group of `C_d : y² = x³ − d²x` (nt-prop0 §1.3): the pairs `(a, b)` of squarefree
integers (signs allowed) whose 2-covering `D_{a,b}` is soluble over `ℝ` and over every `ℚ_p`. By
Lemma 1.2 (`loc_iff_kummer`) over each completion and Silverman X.1.4 (the connecting map of
`0 → C_d[2] → C_d → C_d → 0` is the Kummer map `kummer` under `H¹(ℚ_v, C_d[2]) ≅ (ℚ_v*/ℚ_v*²)²`),
this is the textbook `Sel₂(C_d/ℚ) ⊆ H¹(ℚ, C_d[2]) ≅ (ℚ*/ℚ*²)²`, each square class of `ℚ*` written
by its squarefree integer representative. -/
def Sel2 (d : ℕ) : Set (ℤ × ℤ) :=
  {ab | Squarefree ab.1 ∧ Squarefree ab.2 ∧ Loc ℝ d ab.1 ab.2 ∧
    ∀ (p : ℕ) [Fact p.Prime], Loc ℚ_[p] d ab.1 ab.2}

/-- **Hypothesis CR₃^Sel** (nt-prop0 §1.4). Let `d > 0` be squarefree with `d ≡ 5 (mod 8)`. If the
2-Selmer group `Sel₂(C_d)` (`Sel2 d`) has exactly 8 elements and contains a pair `(a, b)` with
`|a| ≡ 7 (mod 8)`, then the covering `D_{a',b'}` of every `(a', b') ∈ Sel₂(C_d)` has a rational
point.

**Trust statement.** CR₃^Sel is not proved in Lean. In the literature's terms it says: for these
`d`, `dim_{𝔽₂} Sel₂(C_d) = 3` together with the 2-adic shape `|a| ≡ 7 (mod 8)` of one Selmer class
implies `Ш(C_d)[2] = 0`, i.e. `δ(C_d(ℚ)) = Sel₂(C_d)`. Indeed, by Lemma 1.2 over `ℚ`
(`loc_iff_kummer`) and Silverman X.1.4 (the Kummer map `kummer` is the connecting map of the
complete 2-descent, and induces an injection `C_d(ℚ)/2C_d(ℚ) ↪ Sel₂(C_d)`), the conclusion says
that every Selmer class comes from a rational point. Since `C_d(ℚ)[2] = C_d[2]` has order 4,
`dim δ(C_d(ℚ)) = 2 + rank C_d(ℚ)`, so under `#Sel₂ = 8` the conclusion is equivalent to
`rank C_d(ℚ) ≥ 1` (and then to `rank = 1`, `Ш[2] = 0`). Lean derives CR₃^Sel from
`Rank.CertifiedRankRk` (`Rank.certifiedRankSel_of_certifiedRankRk'`, with RK9 and Mordell–Weil
proved), and that from `Rank.CertifiedRankTYZClRk`; see `docs/research/cr3-trust.md`. The positive
rank is provided by:

* for exactly the 2-adic shape `d ≡ 5`, `|a| ≡ 7 (mod 8)` assumed here, Tian–Yuan–Zhang
  (Asian J. Math. 21 (2017): Theorem 3.5 and the argument of the proof of Theorem 3.5(2), §3.3, as
  completed in `docs/research/nt-tyz.md` §4, Proposition N), which gives
  `ord_{s=1} L(C_d, s) = 1`, and Gross–Zagier (Invent. Math. 84 (1986)) with an auxiliary
  imaginary quadratic field (Bump–Friedberg–Hoffstein; `docs/research/pc-audit.md` RK7), which
  gives `rank C_d(ℚ) ≥ 1`; Kolyvagin's published papers enter only inside Tian–Yuan–Zhang.
  Tian–Yuan–Zhang's hypothesis is reached through Corollary 4.4 and Theorem 3.6 of
  `docs/research/tyz-5b.md` (`RouteK.Rank5b.det_M5b_eq_one`, `RouteK.Rank5b.det_M5b_eq_T5b`) and
  Rédei's formula (`RouteK.Redei.redeiFormula`), all proved in Lean.
* as an alternative that is not needed (a preprint; `docs/research/nt-tyz.md` §5.1), Kriz's
  2-converse theorem (arXiv:2002.04767, Theorem 10.13; `E = C_d`, CM by `ℤ[i]`, `p = 2`;
  its standing assumption `f₀ ≥ 4` holds since `d ≥ 21`: by
  Proposition 0 the Selmer class `a` with `|a| ≡ 7 (mod 8)` is a signed divisor of `d`, so
  `d = |a| m` with `m ≡ 3 (mod 8)`)
  together with the corank lemma (manuscript line 1072; Cassels–Tate: the pairing on `Ш/Ш_div` is
  nondegenerate and alternating, so `dim (Ш/Ш_div)[2]` is even, with no finiteness of `Ш` assumed),
  giving `rank C_d(ℚ) = 1` and `Ш(C_d)[2] = 0`.

Compared with `ZInQ.CertifiedRank`, the explicit system `Σ(𝒞_d)`, the Legendre symbols and
Monsky's matrix are not part of the hypothesis: they enter only through Proposition 0
(`Prop0Statement`), which is proved in Lean (`prop0Statement`, `RouteK/Selmer/Prop0.lean`).
`certifiedRank_of_sel` derives `ZInQ.CertifiedRank` from CR₃^Sel and Proposition 0, and
`certifiedRank_of_certifiedRankSel` from CR₃^Sel alone. -/
def CertifiedRankSel : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 →
    (∃ ab ∈ Sel2 d, ab.1.natAbs % 8 = 7) → ∀ ab ∈ Sel2 d, Loc ℚ d ab.1 ab.2

/-- The integer `(−1)^{e₀} 2^{e₁} Π_{p ∣ d} p^{w_p}` standing for a class `(e₀, e₁, w)` of the
Selmer system on the prime factors of `d` (nt-prop0 §0). -/
def classInt (d : ℕ) (e₀ e₁ : ZMod 2) (w : d.primeFactors → ZMod 2) : ℤ :=
  (-1) ^ e₀.val * 2 ^ e₁.val * ∏ p : d.primeFactors, (p : ℤ) ^ (w p).val

/-- The pair `(a(σ), b(σ))` of integers attached to unknowns `σ` of `Σ(𝒞_d)`. -/
def selPair (d : ℕ) (σ : Unknowns d.primeFactors) : ℤ × ℤ :=
  (classInt d σ.a0 σ.a1 σ.u, classInt d σ.b0 σ.b1 σ.v)

/-- **Proposition 0** (nt-prop0 §2.7), in the form `certifiedRank_of_sel` uses. For squarefree
`d ≡ 5 (mod 8)`: `σ` solves `Σ(𝒞_d)` iff `(a(σ), b(σ)) ∈ Sel₂(C_d)`, and every element of
`Sel₂(C_d)` is of the form `(a(σ), b(σ))` (by Lemma G1, no prime outside `{2} ∪ {p ∣ d}` divides a
Selmer pair). The injectivity of `σ ↦ (a(σ), b(σ))` is proved below (`selPair_injective`). -/
def Prop0Statement : Prop :=
  ∀ (d : ℕ) (hd : d % 8 = 5), Squarefree d →
    (∀ σ : Unknowns d.primeFactors,
      (natConfig d (odd_of_mod_eight_eq_five hd)).IsSol σ ↔ selPair d σ ∈ Sel2 d) ∧
    Sel2 d ⊆ Set.range (selPair d)

theorem zmod2_cases (e : ZMod 2) : e = 0 ∨ e = 1 := by revert e; decide

theorem classInt_prod_pos (d : ℕ) (w : d.primeFactors → ZMod 2) :
    0 < ∏ p : d.primeFactors, (p : ℤ) ^ (w p).val :=
  Finset.prod_pos fun p _ => pow_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors p.2).pos) _

theorem classInt_pos_iff (d : ℕ) (e₀ e₁ : ZMod 2) (w : d.primeFactors → ZMod 2) :
    0 < classInt d e₀ e₁ w ↔ e₀ = 0 := by
  have h := classInt_prod_pos d w
  have h2 : (0 : ℤ) < 2 ^ e₁.val := by positivity
  unfold classInt
  rcases zmod2_cases e₀ with rfl | rfl
  · simp only [ZMod.val_zero, pow_zero, one_mul]
    exact iff_of_true (mul_pos h2 h) trivial
  · simp only [show (1 : ZMod 2).val = 1 from rfl, pow_one, neg_mul, one_mul]
    exact iff_of_false (by linarith [mul_pos h2 h]) (by decide)

theorem prime_dvd_classInt_iff {d : ℕ} (hd : Odd d) (e₀ e₁ : ZMod 2) (w : d.primeFactors → ZMod 2)
    (q : d.primeFactors) : (q : ℤ) ∣ classInt d e₀ e₁ w ↔ w q = 1 := by
  obtain ⟨hq, hq2⟩ := prime_ne_two_of_mem_primeFactors hd q.2
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  unfold classInt
  rw [hqZ.dvd_mul, hqZ.dvd_mul, hqZ.dvd_finsetProd_iff]
  have hn1 : ¬(q : ℤ) ∣ (-1) ^ e₀.val := fun h =>
    hqZ.not_isUnit (isUnit_of_dvd_unit h ((isUnit_neg_one).pow _))
  have hn2 : ¬(q : ℤ) ∣ 2 ^ e₁.val := fun h => by
    have := hqZ.dvd_of_dvd_pow h
    have : (q : ℕ) ∣ 2 := by exact_mod_cast this
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp this)
  simp only [hn1, hn2, false_or, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp⟩
    rcases zmod2_cases (w p) with h0 | h1
    · rw [h0, ZMod.val_zero, pow_zero] at hp
      exact absurd (isUnit_of_dvd_one hp) hqZ.not_isUnit
    · have := hqZ.dvd_of_dvd_pow hp
      have hpq : (q : ℕ) ∣ (p : ℕ) := by exact_mod_cast this
      have := (Nat.prime_dvd_prime_iff_eq hq (Nat.prime_of_mem_primeFactors p.2)).mp hpq
      have hpq' : p = q := Subtype.ext this.symm
      rwa [hpq'] at h1
  · intro h
    exact ⟨q, by rw [h]; exact dvd_pow_self _ one_ne_zero⟩

theorem two_dvd_classInt_iff {d : ℕ} (hd : Odd d) (e₀ e₁ : ZMod 2) (w : d.primeFactors → ZMod 2) :
    (2 : ℤ) ∣ classInt d e₀ e₁ w ↔ e₁ = 1 := by
  have hodd : Odd (∏ p : d.primeFactors, (p : ℤ) ^ (w p).val) := by
    refine Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun p _ => Odd.pow ?_
    obtain ⟨hp, hp2⟩ := prime_ne_two_of_mem_primeFactors hd p.2
    exact_mod_cast hp.odd_of_ne_two hp2
  unfold classInt
  rcases zmod2_cases e₁ with rfl | rfl
  · simp only [ZMod.val_zero, pow_zero, mul_one, zero_ne_one, iff_false]
    rw [← even_iff_two_dvd, Int.not_even_iff_odd]
    exact odd_neg_one.pow.mul hodd
  · simp only [show (1 : ZMod 2).val = 1 from rfl, pow_one, iff_true]
    exact Dvd.dvd.mul_right (dvd_mul_left 2 _) _

/-- `σ ↦ (a(σ), b(σ))` is injective: the sign, the parity and the divisibility by each `p ∣ d`
recover the unknowns. -/
theorem selPair_injective {d : ℕ} (hd : Odd d) : Function.Injective (selPair d) := by
  have key : ∀ {e₀ e₁ f₀ f₁ : ZMod 2} {w w' : d.primeFactors → ZMod 2},
      classInt d e₀ e₁ w = classInt d f₀ f₁ w' → e₀ = f₀ ∧ e₁ = f₁ ∧ w = w' := by
    intro e₀ e₁ f₀ f₁ w w' h
    have h0 : e₀ = 0 ↔ f₀ = 0 := by rw [← classInt_pos_iff, h, classInt_pos_iff]
    have h1 : e₁ = 1 ↔ f₁ = 1 := by
      rw [← two_dvd_classInt_iff hd, h, two_dvd_classInt_iff hd]
    refine ⟨?_, ?_, funext fun q => ?_⟩
    · rcases zmod2_cases e₀ with rfl | rfl <;> rcases zmod2_cases f₀ with rfl | rfl <;> simp_all
    · rcases zmod2_cases e₁ with rfl | rfl <;> rcases zmod2_cases f₁ with rfl | rfl <;> simp_all
    · have hq : w q = 1 ↔ w' q = 1 := by
        rw [← prime_dvd_classInt_iff hd e₀ e₁, h, prime_dvd_classInt_iff hd]
      rcases zmod2_cases (w q) with h' | h' <;> rcases zmod2_cases (w' q) with h'' | h'' <;>
        simp_all
  intro σ τ h
  simp only [selPair, Prod.mk.injEq] at h
  obtain ⟨ha0, ha1, hu⟩ := key h.1
  obtain ⟨hb0, hb1, hv⟩ := key h.2
  exact Unknowns.ext ha0 ha1 hb0 hb1 hu hv

/-- Step 2 of nt-prop0 §1.4: the class `natClass d a` of a squarefree divisor `a` of `d` stands
for `a` itself. -/
theorem classInt_natClass {d : ℕ} (hd0 : d ≠ 0) {a : ℤ} (hsq : Squarefree a) (had : a ∣ (d : ℤ)) :
    classInt d (natClass d a).1 (natClass d a).2.1 (natClass d a).2.2 = a := by
  have hn : a.natAbs ∣ d := by
    have := Int.natAbs_dvd_natAbs.mpr had; simpa using this
  have hprod : ∏ p : d.primeFactors,
      (p : ℤ) ^ (if (p.1 : ℤ) ∣ a then (1 : ZMod 2) else 0).val = (a.natAbs : ℤ) := by
    rw [Finset.prod_coe_sort d.primeFactors (fun p : ℕ =>
      (p : ℤ) ^ (if (p : ℤ) ∣ a then (1 : ZMod 2) else 0).val)]
    have : ∀ p ∈ d.primeFactors, (p : ℤ) ^ (if (p : ℤ) ∣ a then (1 : ZMod 2) else 0).val =
        if p ∣ a.natAbs then (p : ℤ) else 1 := fun p _ => by
      by_cases h : p ∣ a.natAbs
      · rw [ite_eq_left (Int.natCast_dvd.mpr h), ite_eq_left h]
        exact pow_one _
      · rw [ite_eq_right (fun h' => h (Int.natCast_dvd.mp h')), ite_eq_right h]
        exact pow_zero _
    rw [Finset.prod_congr rfl this, ← Finset.prod_filter, Nat.primeFactors_filter_dvd_of_dvd hd0 hn,
      ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hsq)]
  simp only [natClass, classInt, ZMod.val_zero, pow_zero, mul_one, hprod, signBit]
  rcases lt_or_ge a 0 with h | h
  · rw [ite_eq_left h, show (1 : ZMod 2).val = 1 from rfl, pow_one, Int.ofNat_natAbs_of_nonpos h.le]
    ring
  · rw [ite_eq_right (not_lt.mpr h), ZMod.val_zero, pow_zero, one_mul, Int.natAbs_of_nonneg h]

/-- A squarefree integer that is a square in `ℚ` is `1`. -/
theorem eq_one_of_squarefree_of_isSquare {z : ℤ} (hz : Squarefree z) (h : IsSquare (z : ℚ)) :
    z = 1 := by
  obtain ⟨r, rfl⟩ := Rat.isSquare_intCast_iff.mp h
  rcases Int.isUnit_iff.mp (hz r dvd_rfl) with rfl | rfl <;> rfl

/-- Steps 3–5 of nt-prop0 §1.4: a rational point on the covering of `(a, b)`, with `a` squarefree
and `|a| ≡ 7 (mod 8)`, gives a point of `C_d` with `x ≠ 0` and `x ∈ a ℚ*²`. -/
theorem exists_point_of_loc {d : ℕ} (hd : d ≠ 0) {a b : ℤ} (hsq : Squarefree a)
    (ha7 : a.natAbs % 8 = 7) (hb : b ≠ 0) (h : Loc ℚ d a b) :
    ∃ x y : ℚ, y ^ 2 = x ^ 3 - (d : ℚ) ^ 2 * x ∧ x ≠ 0 ∧ IsSquare (x / a) := by
  have ha : (a : ℚ) ≠ 0 := by
    have : a ≠ 0 := by rintro rfl; simp at ha7
    exact_mod_cast this
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  rcases h with ⟨hsa, -⟩ | ⟨x, ⟨r₁, e₁⟩, ⟨r₂, e₂⟩, ⟨r₃, e₃⟩⟩
  · rw [eq_one_of_squarefree_of_isSquare hsq hsa] at ha7; simp at ha7
  have f₁ : x = a * r₁ ^ 2 := by rw [sq, ← e₁]; field_simp
  have f₂ : x - d = b * r₂ ^ 2 := by rw [sq, ← e₂]; field_simp
  have f₃ : x + d = a * b * r₃ ^ 2 := by rw [sq, ← e₃]; field_simp
  refine ⟨x, a * b * r₁ * r₂ * r₃, ?_, ?_, ⟨r₁, e₁⟩⟩
  · rw [show x ^ 3 - (d : ℚ) ^ 2 * x = (a * r₁ ^ 2) * (b * r₂ ^ 2) * (a * b * r₃ ^ 2) by
      rw [← f₁, ← f₂, ← f₃]; ring]
    ring
  · rintro rfl
    have hr₃ : r₃ ≠ 0 := by rintro rfl; apply hd'; linear_combination f₃
    have g : b * (a * r₃ ^ 2 + r₂ ^ 2) = 0 := by linear_combination -f₂ - f₃
    have g' : ((-a : ℤ) : ℚ) = (r₂ / r₃) ^ 2 := by
      push_cast; field_simp; linear_combination -(mul_eq_zero.mp g).resolve_left hb'
    have := eq_one_of_squarefree_of_isSquare (fun x hx => hsq x (dvd_neg.mp hx))
      ⟨r₂ / r₃, by rw [g', sq]⟩
    rw [show a = -1 by omega] at ha7; simp at ha7

/-- **CR₃ from CR₃^Sel and Proposition 0** (nt-prop0 §1.4, steps 1–5). -/
theorem certifiedRank_of_sel (hsel : CertifiedRankSel) (h0 : Prop0Statement) : CertifiedRank := by
  intro d a hd hsqd hsqa had ha7 hcard ⟨σ, hσ, hfirst⟩
  have hd0 : d ≠ 0 := by omega
  have hodd := odd_of_mod_eight_eq_five hd
  obtain ⟨hiff, hsurj⟩ := h0 d hd hsqd
  have hmem : selPair d σ ∈ Sel2 d := (hiff σ).1 ((Config.mem_sols _).mp hσ)
  have hA : (selPair d σ).1 = a := by
    have h1 : σ.a0 = (natClass d a).1 := congrArg Prod.fst hfirst
    have h2 : σ.a1 = (natClass d a).2.1 := congrArg (fun t => t.2.1) hfirst
    have h3 : σ.u = (natClass d a).2.2 := congrArg (fun t => t.2.2) hfirst
    simp only [selPair, h1, h2, h3]
    exact classInt_natClass hd0 hsqa had
  have hS : Sel2 d = selPair d '' ((natConfig d hodd).sols : Set (Unknowns d.primeFactors)) := by
    ext ab
    constructor
    · intro hab
      obtain ⟨τ, rfl⟩ := hsurj hab
      exact ⟨τ, (Config.mem_sols _).mpr ((hiff τ).2 hab), rfl⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact (hiff τ).1 ((Config.mem_sols _).mp hτ)
  have hncard : (Sel2 d).ncard = 8 := by
    rw [hS, Set.ncard_image_of_injective _ (selPair_injective hodd), Set.ncard_coe_finset, hcard]
  have hloc := hsel d hd hsqd hncard ⟨_, hmem, by rw [hA]; exact ha7⟩ _ hmem
  rw [hA] at hloc
  exact exists_point_of_loc hd0 hsqa ha7 hmem.2.1.ne_zero hloc

end ZInQ.RouteK.Selmer
