import ZInQKernel.Main
import ZInQKernel.External.GreenTaoDense

/-!
# The main theorem with Green–Tao (dense form) discharged

`ZInQ.greenTaoDense` (Szemerédi's theorem in the primes, proved in `ZInQKernel/External/GreenTaoDense`
from the vendored Green–Tao library `GreenTaoVendor`) discharges the hypothesis `GreenTaoDense` of
the `_of_greenTaoDense` variants of `ZInQKernel/Main.lean`. This module is separate so that
`ZInQKernel.Main` and the main theorem do not import the vendored library.
-/

namespace ZInQ

/-- **Theorem 1.1** from 6C_min, CR₃ and the density part of Proposition D (`GoodPrimeDensity`),
with Szemerédi's theorem in the primes proved (`ZInQ.greenTaoDense`). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_goodPrimeDensity
    (hH : SixContactMin) (hCR : CertifiedRank) (hD : GoodPrimeDensity) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_greenTaoDense hH hCR greenTaoDense hD

/-- **Theorem 1.1** from 6C_min, CR₃^Sel (`RouteK.Selmer.CertifiedRankSel`) and the density part of
Proposition D (`GoodPrimeDensity`), with Szemerédi's theorem in the primes proved
(`ZInQ.greenTaoDense`). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_goodPrimeDensity
    (hH : SixContactMin) (hCRS : RouteK.Selmer.CertifiedRankSel) (hD : GoodPrimeDensity) :
    FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_greenTaoDense hH hCRS
    greenTaoDense hD

end ZInQ
