# Fowler: Proposition 2·7

**Result:** `HDec.CMBranch.FowlerBridges.fowlerProp27_of_print` derives the live
`fowlerProp27` row from `FowlerProp27Print` alone. The statement uses Fowler's proper ideal class
number (p. 613), in the proposition as read from p. 615 on fork issue #14, comment 6973387139.

All four new Lean files compile. They prove the square-index formula for the trace discriminant, both
printed conditions on the discriminant, finiteness of the Picard group, properness iff invertibility, and
the class number equality `card_pic_eq_properClassNumber`. That equality is available independently for
`cmjDegree`. The axiom checks contain only `propext`, `Classical.choice` and `Quot.sound`.
`#discharges` confirmed the live row and its sole remaining assumption. The dry run changes both H counts
from 4 LEAF / 25 GLUE to 5 LEAF / 24 GLUE on 29 rows. No fold was applied.

**Open:** The correspondence with primitive positive definite forms modulo `SL₂(ℤ)` (Cox,
Theorem 7.7) still needs the two quotient maps. `CoxFormClassEquivalence` specifies that goal; the Fowler
provider does not assume it.

**Locator:** The `orderDisc` comment now cites Cox eq. (7.3); Lemma 7.2 is the index statement.
The locator was committed separately, without a rebuild. No error was identified in the manuscript
application at L585–593. See `docs/research/fowler-bridges.md` and `scratch/fowler-bridges/`.
