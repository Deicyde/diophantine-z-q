import ZInQKernel.Contrib.PoleRC.LocalP

/-!
# The torsion classes of `E_ℓ` are local Kummer classes, over any field

Elliot's local Selmer calculation (retained source S12, `parity-frozen-4eaee875.tex`) works in
the Kummer coordinates `(x + 3ℓ, x − ℓ)` (S12 line 252; the Kummer map with its root
replacements is recalled at S12 lines 233–241, Silverman X.1.4). In these coordinates the
rational two-torsion points have the classes (S12 lines 318–324)

* `O ↦ (1, 1)`, `(ℓ, 0) ↦ τ₁ = (ℓ, 1)`, `(−3ℓ, 0) ↦ τ₂ = (3, −ℓ)`, `(0, 0) ↦ τ₁τ₂ = (3ℓ, −ℓ)`.

In the x-form `LocM` of `Defs.lean` this is: `x = ℓ`, `x = −3ℓ`, `x = 0` are witnesses for
`τ₁`, `τ₂`, `τ₁τ₂` (`locM_tau1`, `locM_tau2`, `locM_tau12`). Together with the square-class
invariance of `LocM` (`locM_congr_sq`; the Kummer image is a subset of `(K*/K*²)²`), every pair
in the square class of a torsion class is in `LocM` (`locM_of_torsion`). These are the
sufficiency ("if") halves of the local images at `3` and at `q ∣ ℓ` (S12 lines 349–357: "they
generate the entire local image"), and the torsion part of the image at `2`.
-/

namespace ZInQ.Manuscript.PoleRC

open ZInQ.RouteK.Selmer

section Field

variable {K : Type*} [Field K]

/-- **`LocM` depends only on the square classes of `a` and `b`** (with the same witness `x`). -/
theorem locM_mul_sq_iff {ℓ a b s t : K} (hs : s ≠ 0) (ht : t ≠ 0) :
    LocM K ℓ (a * s ^ 2) (b * t ^ 2) ↔ LocM K ℓ a b := by
  have h1 : ∀ x : K, x / (a * s ^ 2) = x / a / s ^ 2 := fun x => by rw [div_div]
  have h2 : ∀ x : K, x / (b * t ^ 2) = x / b / t ^ 2 := fun x => by rw [div_div]
  have h3 : ∀ x : K, x / (a * s ^ 2 * (b * t ^ 2)) = x / (a * b) / (s * t) ^ 2 := fun x => by
    rw [div_div]; ring_nf
  simp only [LocM, isSquare_mul_sq_iff hs, isSquare_mul_sq_iff ht, h1, h2, h3,
    isSquare_div_sq_iff hs, isSquare_div_sq_iff ht, isSquare_div_sq_iff (mul_ne_zero hs ht)]

/-- **Square-class invariance of `LocM`**, in the form `a ≡ a'`, `b ≡ b'`. -/
theorem locM_congr_sq {ℓ a b a' b' : K} (ha : SqEq a a') (hb : SqEq b b') :
    LocM K ℓ a b ↔ LocM K ℓ a' b' := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact locM_mul_sq_iff hs ht

/-- The class of `O`. -/
theorem locM_one_one (ℓ : K) : LocM K ℓ 1 1 :=
  Or.inl ⟨⟨1, by ring⟩, ⟨1, by ring⟩⟩

/-- The class `τ₁ = (ℓ, 1)` of `(ℓ, 0)` (S12 line 321): the witness `x = ℓ`. -/
theorem locM_tau1 {ℓ : K} (hℓ : ℓ ≠ 0) : LocM K ℓ ℓ 1 := by
  refine Or.inr ⟨ℓ, ⟨2, ?_⟩, ⟨0, by ring⟩, ⟨1, ?_⟩⟩
  · rw [show ℓ + 3 * ℓ = 4 * ℓ by ring, mul_div_assoc, div_self hℓ]; ring
  · rw [mul_one ℓ, div_self hℓ, mul_one]

/-- The class `τ₂ = (3, −ℓ)` of `(−3ℓ, 0)` (S12 line 321): the witness `x = −3ℓ`. -/
theorem locM_tau2 {ℓ : K} (h3 : (3 : K) ≠ 0) (hℓ : ℓ ≠ 0) : LocM K ℓ 3 (-ℓ) := by
  have hnℓ : -ℓ ≠ 0 := neg_ne_zero.mpr hℓ
  refine Or.inr ⟨-3 * ℓ, ⟨0, by ring⟩, ⟨2, ?_⟩, ⟨1, ?_⟩⟩
  · rw [show -3 * ℓ - ℓ = 4 * -ℓ by ring, mul_div_assoc, div_self hnℓ]; ring
  · rw [show (3 : K) * -ℓ = -3 * ℓ by ring, div_self (mul_ne_zero (neg_ne_zero.mpr h3) hℓ)]
    ring

/-- The class `τ₁τ₂ = (3ℓ, −ℓ)` of `(0, 0)`: the witness `x = 0`. -/
theorem locM_tau12 {ℓ : K} (h3 : (3 : K) ≠ 0) (hℓ : ℓ ≠ 0) : LocM K ℓ (3 * ℓ) (-ℓ) := by
  refine Or.inr ⟨0, ⟨1, ?_⟩, ⟨1, ?_⟩, ⟨0, by ring⟩⟩
  · rw [zero_add, div_self (mul_ne_zero h3 hℓ)]; ring
  · rw [zero_sub, div_self (neg_ne_zero.mpr hℓ)]; ring

/-- **Every pair in the square class of a torsion class is a local Kummer class** (over any
field in which `3 ≠ 0`). -/
theorem locM_of_torsion {ℓ a b : K} (h3 : (3 : K) ≠ 0) (hℓ : ℓ ≠ 0)
    (h : (SqEq a 1 ∧ SqEq b 1) ∨ (SqEq a ℓ ∧ SqEq b 1) ∨ (SqEq a 3 ∧ SqEq b (-ℓ)) ∨
      (SqEq a (3 * ℓ) ∧ SqEq b (-ℓ))) : LocM K ℓ a b := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact (locM_congr_sq ha hb).mpr (locM_one_one ℓ)
  · exact (locM_congr_sq ha hb).mpr (locM_tau1 hℓ)
  · exact (locM_congr_sq ha hb).mpr (locM_tau2 h3 hℓ)
  · exact (locM_congr_sq ha hb).mpr (locM_tau12 h3 hℓ)

end Field

end ZInQ.Manuscript.PoleRC
