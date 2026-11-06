import Mathlib

/-!
# Residue computations modulo seven

Blueprint: `model/field/residue-checks.md`.

`3² ≡ 2`, `75 - 53·3 = -84 ≡ 0`, `3 - 3 = 0` modulo `7`, and `-1` is not a square modulo `7`.
They say that `s ↦ 3` defines a ring homomorphism `ℤ[s] → 𝔽₇` killing `d` and `δ`. Checked by
`decide` in the kernel.
-/

namespace ZInQ

theorem residues_mod_seven :
    (3 : ZMod 7) ^ 2 = 2 ∧ (75 - 53 * 3 : ℤ) = -84 ∧ (75 - 53 * 3 : ZMod 7) = 0 ∧
      (3 - 3 : ZMod 7) = 0 ∧ ∀ t : ZMod 7, t ^ 2 ≠ -1 := by
  decide

theorem not_isSquare_neg_one_zmod_seven : ¬ IsSquare (-1 : ZMod 7) := by
  rintro ⟨t, ht⟩
  exact residues_mod_seven.2.2.2.2 t (by rw [pow_two, ht])

end ZInQ
