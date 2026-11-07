import Mathlib

/-!
# The witness-count arithmetic

Blueprint: `syntax/recipes/witness-count-identity.md`.

Closed identities between natural numbers below `2⁴⁰`, checked by the kernel's `Nat`
arithmetic.
-/

namespace ZInQ.Syntax

/-- **The witness-count arithmetic.** -/
theorem witness_count_arith :
    3 + 79 * (5 + 140604) + 3 * (5 + 1) + 196 * (5 + 6) + 190 * (5 + 35134) = 17786698 ∧
      3 + 5 * 140604 + 54051 * (5 + 140604) + 4 * (5 + 1) + 125327 * (5 + 6) +
        98382 * (5 + 35134) + 15845 * (5 + 17786698) = 292889492836 ∧
      8 * 5 + 5 * 140654 + 292889492836 + 53 = 292890196199 ∧
      5 + 292890196199 + 35282 = 292890231486 ∧ 406 + 292890231486 = 292890231892 ∧
      7 + 292890231892 = 292890231899 ∧ 5 + 292890231899 = 292890231904 := by
  decide

/-- The total variable counts: witnesses plus parameters. -/
theorem variable_count_arith :
    17786698 + 20 = 17786718 ∧ 292889492836 + 25 = 292889492861 ∧
      292890196199 + 11 = 292890196210 ∧ 292890231486 + 6 = 292890231492 ∧
      292890231892 + 6 = 292890231898 ∧ 292890231899 + 6 = 292890231905 ∧
      292890231904 + 1 = 292890231905 := by
  decide

end ZInQ.Syntax
