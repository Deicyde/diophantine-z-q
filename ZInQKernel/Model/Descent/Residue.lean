import ZInQKernel.Model.Descent.Factor

/-!
# Valuation bounds and residue maps at a prime of `ℤ[√2]`

Helpers for `model/descent/reduction-torsion.md`.

For a prime `π` of `ℤ[s]`:

* `VGe π k x` means `v_π(x) ≥ k` (with `v_π(0) = ∞`); it is stable under sums and
  `VGe π k x → VGe π l y → VGe π (k + l) (x y)`;
* for a surjective ring homomorphism `ρ : ℤ[s] → 𝔽_p` with kernel `(π)`, `res π ρ : K₀ → 𝔽_p`
  is the residue map of the local ring `ℤ[s]_(π)`: `res (a / b) = ρ a / ρ b` for `π ∤ b`. It is
  additive and multiplicative on `π`-integral elements (`VGe π 0`).
-/

namespace ZInQ

open QuadraticAlgebra K0

/-! ### Valuation bounds -/

/-- `v_π(x) ≥ k`, with the convention `v_π(0) = ∞`. -/
def VGe (π : Zs) (k : ℤ) (x : K0) : Prop := x = 0 ∨ k ≤ vp π x

section VGe

variable {π : Zs} {k l : ℤ} {x y : K0}

theorem VGe.zero (π : Zs) (k : ℤ) : VGe π k 0 := Or.inl rfl

theorem vge_iff (hx : x ≠ 0) : VGe π k x ↔ k ≤ vp π x := by
  simp [VGe, hx]

theorem VGe.mono (h : VGe π k x) (hlk : l ≤ k) : VGe π l x := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans hlk h)

variable (hπ : Prime π)
include hπ

theorem VGe.neg (h : VGe π k x) : VGe π k (-x) := by
  rcases h with h | h
  · left; rw [h, neg_zero]
  · right; rwa [vp_neg hπ]

theorem VGe.add (hx : VGe π k x) (hy : VGe π k y) : VGe π k (x + y) := by
  by_cases hx0 : x = 0
  · rwa [hx0, zero_add]
  by_cases hy0 : y = 0
  · rwa [hy0, add_zero]
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  right
  rw [vge_iff hx0] at hx
  rw [vge_iff hy0] at hy
  exact le_trans (le_min hx hy) (min_le_vp_add hπ hx0 hy0 hxy)

theorem VGe.sub (hx : VGe π k x) (hy : VGe π k y) : VGe π k (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hπ (hy.neg hπ)

theorem VGe.mul (hx : VGe π k x) (hy : VGe π l y) : VGe π (k + l) (x * y) := by
  by_cases hx0 : x = 0
  · left; rw [hx0, zero_mul]
  by_cases hy0 : y = 0
  · left; rw [hy0, mul_zero]
  right
  rw [vge_iff hx0] at hx
  rw [vge_iff hy0] at hy
  rw [vp_mul hπ hx0 hy0]; omega

theorem VGe.pow (hx : VGe π k x) (n : ℕ) : VGe π (n * k) (x ^ n) := by
  induction n with
  | zero => right; simp [vp_one hπ]
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul hπ hx
    convert this using 1; push_cast; ring

theorem VGe.div (hx : VGe π k x) (hy : y ≠ 0) : VGe π (k - vp π y) (x / y) := by
  by_cases hx0 : x = 0
  · left; rw [hx0, zero_div]
  right
  rw [vge_iff hx0] at hx
  rw [vp_div hπ hx0 hy]; omega

theorem vge_toK0 (a : Zs) : VGe π 0 (Zs.toK0 a) := Or.inr (vp_nonneg hπ a)

theorem vge_natCast (n : ℕ) : VGe π 0 (n : K0) := by
  rw [← toK0_natCast]; exact vge_toK0 hπ _

theorem vge_intCast (n : ℤ) : VGe π 0 (n : K0) := by
  rw [← toK0_intCast]; exact vge_toK0 hπ _

theorem vge_ofNat (n : ℕ) [n.AtLeastTwo] : VGe π 0 (OfNat.ofNat n : K0) := by
  simpa only [Nat.cast_ofNat] using vge_natCast hπ (OfNat.ofNat n)

theorem vge_one : VGe π 0 (1 : K0) := by
  have := vge_natCast hπ 1; simpa using this

/-- If `v(y) > v(x)` then `v(x + y) = v(x)`. -/
theorem vp_add_eq_of_vge (hx : x ≠ 0) (hy : VGe π (vp π x + 1) y) :
    vp π (x + y) = vp π x := by
  by_cases hy0 : y = 0
  · rw [hy0, add_zero]
  rw [vge_iff hy0] at hy
  rw [vp_add_eq_min_of_ne hπ hx hy0 (by omega)]
  omega

theorem add_ne_zero_of_vge (hx : x ≠ 0) (hy : VGe π (vp π x + 1) y) : x + y ≠ 0 := by
  intro h
  by_cases hy0 : y = 0
  · rw [hy0, add_zero] at h; exact hx h
  rw [vge_iff hy0] at hy
  have : y = -x := by linear_combination h
  rw [this, vp_neg hπ] at hy; omega

/-- A `π`-adic unit: `1 + z` with `v(z) ≥ 1` has valuation zero. -/
theorem vp_one_add (hz : VGe π 1 x) : vp π (1 + x) = 0 := by
  have := vp_add_eq_of_vge hπ one_ne_zero (by rw [vp_one hπ]; exact hz)
  rwa [vp_one hπ] at this

theorem one_add_ne_zero (hz : VGe π 1 x) : 1 + x ≠ 0 :=
  add_ne_zero_of_vge hπ one_ne_zero (by rw [vp_one hπ]; exact hz)

omit hπ in
theorem VGe.of_vp_eq (hx : x ≠ 0) (h : vp π x = k) : VGe π k x := Or.inr h.ge

omit hπ in
theorem vp_eq_of_vge (hx : x ≠ 0) (h : VGe π k x) (h' : ¬VGe π (k + 1) x) : vp π x = k := by
  rw [vge_iff hx] at h h'; omega

end VGe

/-! ### Elements of the local ring as fractions -/

section Fractions

variable {π : Zs} (hπ : Prime π)
include hπ

/-- A `π`-integral element is `a / b` with `π ∤ b`. -/
theorem exists_rep_of_vge {x : K0} (hx : VGe π 0 x) :
    ∃ a b : Zs, ¬π ∣ b ∧ x * Zs.toK0 b = Zs.toK0 a := by
  by_cases hx0 : x = 0
  · exact ⟨0, 1, fun h => hπ.not_isUnit (isUnit_of_dvd_one h), by simp [hx0]⟩
  rw [vge_iff hx0] at hx
  obtain ⟨a, b, hb, rfl⟩ := exists_eq_div_Zs x
  have ha : a ≠ 0 := by rintro rfl; simp at hx0
  obtain ⟨i, a', ha', rfl⟩ := WfDvdMonoid.max_power_factor ha hπ.irreducible
  obtain ⟨j, b', hb', rfl⟩ := WfDvdMonoid.max_power_factor hb hπ.irreducible
  have ha0 : a' ≠ 0 := right_ne_zero_of_mul ha
  have hb0 : b' ≠ 0 := right_ne_zero_of_mul hb
  have hπ0 := toK0_ne_zero hπ.ne_zero
  simp only [map_mul, map_pow] at hx ⊢
  rw [vp_div hπ (mul_ne_zero (pow_ne_zero _ hπ0) (toK0_ne_zero ha0))
    (mul_ne_zero (pow_ne_zero _ hπ0) (toK0_ne_zero hb0)),
    vp_mul hπ (pow_ne_zero _ hπ0) (toK0_ne_zero ha0),
    vp_mul hπ (pow_ne_zero _ hπ0) (toK0_ne_zero hb0), vp_pow hπ, vp_pow hπ, vp_self hπ,
    (vp_eq_zero_iff hπ ha0).mpr ha', (vp_eq_zero_iff hπ hb0).mpr hb'] at hx
  have hij : j ≤ i := by push_cast at hx; omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  refine ⟨π ^ k * a', b', hb', ?_⟩
  have hb0' := toK0_ne_zero hb0
  simp only [map_mul, map_pow]
  field_simp
  ring

theorem vge_one_iff_of_rep {x : K0} {a b : Zs} (hb : ¬π ∣ b) (h : x * Zs.toK0 b = Zs.toK0 a) :
    VGe π 1 x ↔ π ∣ a := by
  have hb0 : b ≠ 0 := by rintro rfl; exact hb (dvd_zero _)
  have hb' := toK0_ne_zero hb0
  have hx : x = Zs.toK0 a / Zs.toK0 b := by rw [← h]; field_simp
  by_cases ha : a = 0
  · subst ha; simp only [map_zero, zero_div] at hx; subst hx
    exact ⟨fun _ => dvd_zero _, fun _ => VGe.zero _ _⟩
  rw [hx, vge_iff (div_ne_zero (toK0_ne_zero ha) hb'), vp_div hπ (toK0_ne_zero ha) hb',
    (vp_eq_zero_iff hπ hb0).mpr hb, sub_zero, ← vp_pos_iff hπ ha]
  omega

end Fractions

/-! ### The residue map -/

section Residue

variable {p : ℕ} [Fact p.Prime] {π : Zs} (hπ : Prime π) (ρ : Zs →+* ZMod p)
  (hρ : ∀ a, ρ a = 0 ↔ π ∣ a)

open Classical in
/-- The residue map `ℤ[s]_(π) → 𝔽_p`, `a / b ↦ ρ a / ρ b` (and `0` off the local ring). -/
noncomputable def res (π : Zs) (ρ : Zs →+* ZMod p) (x : K0) : ZMod p :=
  if h : ∃ ab : Zs × Zs, ¬π ∣ ab.2 ∧ x * Zs.toK0 ab.2 = Zs.toK0 ab.1 then
    ρ h.choose.1 / ρ h.choose.2
  else 0

include hρ

theorem res_eq {x : K0} {a b : Zs} (hb : ¬π ∣ b) (h : x * Zs.toK0 b = Zs.toK0 a) :
    res π ρ x = ρ a / ρ b := by
  have hex : ∃ ab : Zs × Zs, ¬π ∣ ab.2 ∧ x * Zs.toK0 ab.2 = Zs.toK0 ab.1 := ⟨(a, b), hb, h⟩
  rw [res, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨hb', h'⟩ := hex.choose_spec
  set a' := hex.choose.1
  set b' := hex.choose.2
  have hρb : ρ b ≠ 0 := fun h0 => hb ((hρ b).mp h0)
  have hρb' : ρ b' ≠ 0 := fun h0 => hb' ((hρ b').mp h0)
  have e : a * b' = a' * b := by
    apply Zs.toK0_injective
    rw [map_mul, map_mul, ← h, ← h']; ring
  rw [div_eq_div_iff hρb' hρb, ← map_mul, ← map_mul, ← e, mul_comm]

include hπ

theorem res_toK0 (a : Zs) : res π ρ (Zs.toK0 a) = ρ a := by
  rw [res_eq ρ hρ (a := a) (b := 1) (fun h => hπ.not_isUnit (isUnit_of_dvd_one h)) (by simp)]
  simp

theorem res_add {x y : K0} (hx : VGe π 0 x) (hy : VGe π 0 y) :
    res π ρ (x + y) = res π ρ x + res π ρ y := by
  obtain ⟨a, b, hb, h⟩ := exists_rep_of_vge hπ hx
  obtain ⟨c, d, hd, h'⟩ := exists_rep_of_vge hπ hy
  have hbd : ¬π ∣ b * d := fun h0 => (hπ.dvd_or_dvd h0).elim hb hd
  have hρb : ρ b ≠ 0 := fun h0 => hb ((hρ b).mp h0)
  have hρd : ρ d ≠ 0 := fun h0 => hd ((hρ d).mp h0)
  rw [res_eq ρ hρ hb h, res_eq ρ hρ hd h', res_eq ρ hρ (a := a * d + c * b) hbd (by
    simp only [map_mul, map_add, ← h, ← h']; ring)]
  rw [div_add_div _ _ hρb hρd]; simp only [map_add, map_mul]; ring

theorem res_mul {x y : K0} (hx : VGe π 0 x) (hy : VGe π 0 y) :
    res π ρ (x * y) = res π ρ x * res π ρ y := by
  obtain ⟨a, b, hb, h⟩ := exists_rep_of_vge hπ hx
  obtain ⟨c, d, hd, h'⟩ := exists_rep_of_vge hπ hy
  have hbd : ¬π ∣ b * d := fun h0 => (hπ.dvd_or_dvd h0).elim hb hd
  rw [res_eq ρ hρ hb h, res_eq ρ hρ hd h', res_eq ρ hρ (a := a * c) hbd (by
    simp only [map_mul, ← h, ← h']; ring)]
  simp only [map_mul]; ring

theorem res_neg {x : K0} (hx : VGe π 0 x) : res π ρ (-x) = -res π ρ x := by
  obtain ⟨a, b, hb, h⟩ := exists_rep_of_vge hπ hx
  rw [res_eq ρ hρ hb h, res_eq ρ hρ (a := -a) hb (by simp only [map_neg, ← h]; ring)]
  simp only [map_neg]; ring

theorem res_sub {x y : K0} (hx : VGe π 0 x) (hy : VGe π 0 y) :
    res π ρ (x - y) = res π ρ x - res π ρ y := by
  rw [sub_eq_add_neg, res_add hπ ρ hρ hx (hy.neg hπ), res_neg hπ ρ hρ hy, ← sub_eq_add_neg]

theorem res_pow {x : K0} (hx : VGe π 0 x) (n : ℕ) : res π ρ (x ^ n) = res π ρ x ^ n := by
  induction n with
  | zero => simpa using res_toK0 hπ ρ hρ 1
  | succ n ih =>
    rw [pow_succ, res_mul hπ ρ hρ (by simpa using hx.pow hπ n) hx, ih, pow_succ]

theorem res_eq_zero_iff {x : K0} (hx : VGe π 0 x) : res π ρ x = 0 ↔ VGe π 1 x := by
  obtain ⟨a, b, hb, h⟩ := exists_rep_of_vge hπ hx
  have hρb : ρ b ≠ 0 := fun h0 => hb ((hρ b).mp h0)
  rw [res_eq ρ hρ hb h, div_eq_zero_iff, vge_one_iff_of_rep hπ hb h, ← hρ a]
  tauto

theorem res_natCast (n : ℕ) : res π ρ (n : K0) = n := by
  rw [← toK0_natCast, res_toK0 hπ ρ hρ, map_natCast]

theorem res_ofNat (n : ℕ) [n.AtLeastTwo] : res π ρ (OfNat.ofNat n : K0) = OfNat.ofNat n := by
  simpa only [Nat.cast_ofNat] using res_natCast hπ ρ hρ (OfNat.ofNat n)

theorem res_one : res π ρ 1 = 1 := by simpa using res_natCast hπ ρ hρ 1

theorem res_zero : res π ρ 0 = 0 := by simpa using res_natCast hπ ρ hρ 0

theorem res_div {x y : K0} (hx : VGe π 0 x) (hy : VGe π 0 y) (hy' : vp π y = 0) (hy0 : y ≠ 0) :
    res π ρ (x / y) = res π ρ x / res π ρ y := by
  have hxy : VGe π 0 (x / y) := by have := hx.div hπ hy0; rwa [hy', sub_zero] at this
  have hry : res π ρ y ≠ 0 := by
    rw [ne_eq, res_eq_zero_iff hπ ρ hρ hy, vge_iff hy0]; omega
  rw [eq_div_iff hry, ← res_mul hπ ρ hρ hxy hy, div_mul_cancel₀ _ hy0]

end Residue

end ZInQ
