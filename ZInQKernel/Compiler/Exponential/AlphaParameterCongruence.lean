import ZInQ.AlphaParameterCongruence
import ZInQ.AlphaAddition
import Mathlib.Data.Int.GCD

/-!
# Parameter congruence of the alpha sequence

Blueprint: `compiler/natural/exponential/alpha-parameter-congruence.md`.

`b ≡ b' (mod d)` implies `α_b(n) ≡ α_{b'}(n) (mod d)` (upstream `alphaZ_emod_eq_of_mod_eq`), and
`α_2(n) = n` (upstream `alphaZ_two_left`).
-/

namespace ZInQ.AlphaPower

/-- Congruence in the parameter: `b ≡ b' (mod d)` gives `α_b(n) ≡ α_{b'}(n) (mod d)`. -/
theorem alphaZ_modEq_of_modEq {b b' d : ℕ} (h : b ≡ b' [MOD d]) (n : ℕ) :
    alphaZ b n ≡ alphaZ b' n [ZMOD d] :=
  alphaZ_emod_eq_of_mod_eq d b b' n h

/-- `α_2(n) = n`. -/
theorem alphaZ_two (n : ℕ) : alphaZ 2 n = n :=
  alphaZ_two_left n

/-- `b ≡ 2 (mod d)` gives `α_b(n) ≡ n (mod d)`. -/
theorem alphaZ_modEq_index {b d : ℕ} (h : b ≡ 2 [MOD d]) (n : ℕ) :
    alphaZ b n ≡ n [ZMOD d] := by
  have := alphaZ_modEq_of_modEq h n
  rwa [alphaZ_two] at this

end ZInQ.AlphaPower
