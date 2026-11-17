import ZInQKernel.Main
import ZInQKernel.External.GreenTaoDense
import ZInQKernel.Density.PropDFinal

/-!
# The main theorem with Green–Tao (dense form) and Proposition D discharged

`ZInQ.greenTaoDense` (Szemerédi's theorem in the primes, proved in `ZInQKernel/External/GreenTaoDense`
from the vendored Green–Tao library `GreenTaoVendor`) discharges the hypothesis `GreenTaoDense` of
`exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness_greenTaoDense`
(`ZInQKernel/Main.lean`), and `ZInQ.Density.goodPrimeDensity` (Proposition D, `ZInQKernel/Density/`)
discharges `GoodPrimeDensity`. Together they replace the twenty-two-prime pattern 22P: the headline
below assumes only H (`SixContactMin`) and PC (`PoleCompleteness`). This module is separate so that
`ZInQKernel.Main` does not import the vendored library.
-/

namespace ZInQ

/-- **Theorem 1.1** from 6C_min, PC and the density part of Proposition D (`GoodPrimeDensity`),
with Szemerédi's theorem in the primes proved (`ZInQ.greenTaoDense`). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness_goodPrimeDensity
    (hH : SixContactMin) (hPC : PoleCompleteness) (hD : GoodPrimeDensity) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness_greenTaoDense hH hPC
    greenTaoDense hD

/-- **Theorem 1.1 from H and PC alone (the headline).** Under the minimal six-contact estimate H
(`SixContactMin`, one instance of the manuscript's Theorem 4.1) and pole completeness PC
(`PoleCompleteness`, the manuscript's Theorem 5.2), there is an integer polynomial in
`292890231905` variables, of degree below `2↑↑7` and with coefficients below `2↑↑8`, whose rational
zero projection to the first variable is exactly `ℤ`. The twenty-two-prime pattern 22P is replaced
by route AP, whose hypothesis follows from Szemerédi's theorem in the primes (`ZInQ.greenTaoDense`)
and Proposition D (`ZInQ.Density.goodPrimeDensity`), both proved in Lean. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (hH : SixContactMin) (hPC : PoleCompleteness) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness_goodPrimeDensity hH hPC
    Density.goodPrimeDensity

end ZInQ
