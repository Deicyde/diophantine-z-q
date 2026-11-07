import ZInQKernel.Model.Descent.Residue

/-!
# The residue map at a prime of `ℤ[√2]` into an arbitrary residue field

Helper for `size/formal-multiple/reduction-homomorphism.md`.

The model chapter's residue map `ZInQ.res` takes values in `𝔽_p` (primes of residue degree
one). Here `k` is any field and `ρ : ℤ[s] →+* k` a ring homomorphism with kernel `(π)` (for
instance the quotient map onto `ℤ[s]/(π)`); `resK π ρ : K₀ → k` is the residue map of the local
ring `ℤ[s]_(π)`, `a / b ↦ ρ a / ρ b` for `π ∤ b`. It is additive and multiplicative on
`π`-integral elements (`VGe π 0`). The proofs are those of the model chapter.
-/

namespace ZInQ.Size

open QuadraticAlgebra

variable {k : Type*} [Field k] {π : Zs} (hπ : Prime π) (ρ : Zs →+* k)
  (hρ : ∀ a, ρ a = 0 ↔ π ∣ a)

open Classical in
/-- The residue map `ℤ[s]_(π) → k`, `a / b ↦ ρ a / ρ b` (and `0` off the local ring). -/
noncomputable def resK (π : Zs) (ρ : Zs →+* k) (x : K0) : k :=
  if h : ∃ ab : Zs × Zs, ¬π ∣ ab.2 ∧ x * Zs.toK0 ab.2 = Zs.toK0 ab.1 then
    ρ h.choose.1 / ρ h.choose.2
  else 0

include hρ

theorem resK_eq {x : K0} {a b : Zs} (hb : ¬π ∣ b) (h : x * Zs.toK0 b = Zs.toK0 a) :
    resK π ρ x = ρ a / ρ b := by
  have hex : ∃ ab : Zs × Zs, ¬π ∣ ab.2 ∧ x * Zs.toK0 ab.2 = Zs.toK0 ab.1 := ⟨(a, b), hb, h⟩
  rw [resK, dite_eq_left_of_eq_true (eq_true hex)]
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

theorem resK_toK0 (a : Zs) : resK π ρ (Zs.toK0 a) = ρ a := by
  rw [resK_eq ρ hρ (a := a) (b := 1) (fun h => hπ.not_isUnit (isUnit_of_dvd_one h)) (by simp)]
  simp

theorem resK_add {x y : K0} (hx : VGe π 0 x) (hy : VGe π 0 y) :
    resK π ρ (x + y) = resK π ρ x + resK π ρ y := by
  obtain ⟨a, b, hb, h⟩ := exists_rep_of_vge hπ hx
  obtain ⟨c, d, hd, h'⟩ := exists_rep_of_vge hπ hy
  have hbd : ¬π ∣ b * d := fun h0 => (hπ.dvd_or_dvd h0).elim hb hd
  have hρb : ρ b ≠ 0 := fun h0 => hb ((hρ b).mp h0)
  have hρd : ρ d ≠ 0 := fun h0 => hd ((hρ d).mp h0)
  rw [resK_eq ρ hρ hb h, resK_eq ρ hρ hd h', resK_eq ρ hρ (a := a * d + c * b) hbd (by
    simp only [map_mul, map_add, ← h, ← h']; ring)]
  rw [div_add_div _ _ hρb hρd]; simp only [map_add, map_mul]; ring

theorem resK_mul {x y : K0} (hx : VGe π 0 x) (hy : VGe π 0 y) :
    resK π ρ (x * y) = resK π ρ x * resK π ρ y := by
  obtain ⟨a, b, hb, h⟩ := exists_rep_of_vge hπ hx
  obtain ⟨c, d, hd, h'⟩ := exists_rep_of_vge hπ hy
  have hbd : ¬π ∣ b * d := fun h0 => (hπ.dvd_or_dvd h0).elim hb hd
  rw [resK_eq ρ hρ hb h, resK_eq ρ hρ hd h', resK_eq ρ hρ (a := a * c) hbd (by
    simp only [map_mul, ← h, ← h']; ring)]
  simp only [map_mul]; ring

theorem resK_neg {x : K0} (hx : VGe π 0 x) : resK π ρ (-x) = -resK π ρ x := by
  obtain ⟨a, b, hb, h⟩ := exists_rep_of_vge hπ hx
  rw [resK_eq ρ hρ hb h, resK_eq ρ hρ (a := -a) hb (by simp only [map_neg, ← h]; ring)]
  simp only [map_neg]; ring

theorem resK_sub {x y : K0} (hx : VGe π 0 x) (hy : VGe π 0 y) :
    resK π ρ (x - y) = resK π ρ x - resK π ρ y := by
  rw [sub_eq_add_neg, resK_add hπ ρ hρ hx (hy.neg hπ), resK_neg hπ ρ hρ hy, ← sub_eq_add_neg]

theorem resK_pow {x : K0} (hx : VGe π 0 x) (n : ℕ) : resK π ρ (x ^ n) = resK π ρ x ^ n := by
  induction n with
  | zero => simpa using resK_toK0 hπ ρ hρ 1
  | succ n ih =>
    rw [pow_succ, resK_mul hπ ρ hρ (by simpa using hx.pow hπ n) hx, ih, pow_succ]

theorem resK_eq_zero_iff {x : K0} (hx : VGe π 0 x) : resK π ρ x = 0 ↔ VGe π 1 x := by
  obtain ⟨a, b, hb, h⟩ := exists_rep_of_vge hπ hx
  have hρb : ρ b ≠ 0 := fun h0 => hb ((hρ b).mp h0)
  rw [resK_eq ρ hρ hb h, div_eq_zero_iff, vge_one_iff_of_rep hπ hb h, ← hρ a]
  tauto

theorem resK_natCast (n : ℕ) : resK π ρ (n : K0) = n := by
  rw [← toK0_natCast, resK_toK0 hπ ρ hρ, map_natCast]

theorem resK_ofNat (n : ℕ) [n.AtLeastTwo] : resK π ρ (OfNat.ofNat n : K0) = OfNat.ofNat n := by
  simpa only [Nat.cast_ofNat] using resK_natCast hπ ρ hρ (OfNat.ofNat n)

theorem resK_one : resK π ρ 1 = 1 := by simpa using resK_natCast hπ ρ hρ 1

theorem resK_zero : resK π ρ 0 = 0 := by simpa using resK_natCast hπ ρ hρ 0

theorem resK_div {x y : K0} (hx : VGe π 0 x) (hy : VGe π 0 y) (hy' : vp π y = 0) (hy0 : y ≠ 0) :
    resK π ρ (x / y) = resK π ρ x / resK π ρ y := by
  have hxy : VGe π 0 (x / y) := by have := hx.div hπ hy0; rwa [hy', sub_zero] at this
  have hry : resK π ρ y ≠ 0 := by
    rw [ne_eq, resK_eq_zero_iff hπ ρ hρ hy, vge_iff hy0]; omega
  rw [eq_div_iff hry, ← resK_mul hπ ρ hρ hxy hy, div_mul_cancel₀ _ hy0]

/-- An integral element with nonzero residue has valuation zero. -/
theorem vp_eq_zero_of_resK_ne_zero {x : K0} (hx : VGe π 0 x) (hr : resK π ρ x ≠ 0) :
    x ≠ 0 ∧ vp π x = 0 := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hr (resK_zero hπ ρ hρ)
  refine ⟨hx0, ?_⟩
  have h1 := (resK_eq_zero_iff hπ ρ hρ hx).not.mp hr
  rw [vge_iff hx0] at h1 hx
  omega

end ZInQ.Size
