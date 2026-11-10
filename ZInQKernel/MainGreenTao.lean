import ZInQKernel.Main
import ZInQKernel.External.GreenTaoDense
import ZInQKernel.Density.PropDFinal

/-!
# The main theorem with Green–Tao (dense form) and Proposition D discharged

`ZInQ.greenTaoDense` (Szemerédi's theorem in the primes, proved in `ZInQKernel/External/GreenTaoDense`
from the vendored Green–Tao library `GreenTaoVendor`) discharges the hypothesis `GreenTaoDense` of
the `_of_greenTaoDense` variants of `ZInQKernel/Main.lean`, and `ZInQ.Density.goodPrimeDensity`
(Proposition D, `ZInQKernel/Density/`) discharges `GoodPrimeDensity`. Together they replace the
twenty-two-prime pattern 22P: the last two theorems below assume only 6C_min and CR₃ (or CR₃^Sel).
This module is separate so that `ZInQKernel.Main` and the main theorem do not import the vendored
library.
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

/-- **Theorem 1.1** from 6C_min and CR₃ alone. The twenty-two-prime pattern 22P is replaced by
route AP (`exists_bounded_integer_polynomial_defining_integers_of_goodPrimeAP`), whose hypothesis
follows from Szemerédi's theorem in the primes (`ZInQ.greenTaoDense`) and Proposition D
(`ZInQ.Density.goodPrimeDensity`), both proved in Lean. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank
    (hH : SixContactMin) (hCR : CertifiedRank) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_goodPrimeDensity hH hCR
    Density.goodPrimeDensity

/-- **Theorem 1.1** from 6C_min and CR₃^Sel (`RouteK.Selmer.CertifiedRankSel`) alone; see
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank`. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankSel
    (hH : SixContactMin) (hCRS : RouteK.Selmer.CertifiedRankSel) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_goodPrimeDensity hH hCRS
    Density.goodPrimeDensity

end ZInQ
