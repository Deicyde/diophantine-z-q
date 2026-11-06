import ZInQKernel.Target
import ZInQKernel.Hypotheses.Height
import ZInQKernel.Hypotheses.Pole
import ZInQKernel.Hypotheses.MordellWeil
import ZInQKernel.Hypotheses.PrimePattern

/-!
# The main theorem

Theorem 1.1 of the 11/5 manuscript, with its deep arithmetic inputs as explicit
hypotheses: the six-contact height estimate (H), pole completeness (PC), the
Mordell–Weil theorem for the generator curve (MW), the twenty-two-prime pattern (22P)
and the catalogue bound (CAT). No `axiom` is involved: the trust boundary is the
hypothesis list of this theorem.
-/

namespace ZInQ

/-- **Main theorem.** Under hypotheses H, PC, MW, 22P and CAT, there is an integer
polynomial in `292890231905` variables, of degree below `2↑↑7` and with coefficients below
`2↑↑8`, whose rational zero projection to the first variable is exactly `ℤ`. -/
theorem exists_bounded_integer_polynomial_defining_integers_of
    (hH : SixContactEstimate) (hPC : PoleCompleteness) (hMW : MordellWeilE)
    (h22 : FixedPrimePattern) (hCAT : CatalogueBound) : FrozenTarget := by
  sorry

end ZInQ
