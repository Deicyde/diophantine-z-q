import ZInQKernel.MainLiterature
import ZInQKernel.Contrib.GaussFE.FunctionalEquation5

/-!
# The headline with `HeckeContinuation` and `FunctionalEquation5` discharged

With Gauss's point count proved (`GaussFE.gaussPointCount`), CR₃ in the form
`RouteK.Rank.CertifiedRankTYZClRk` follows from `Literature.TYZThm35ReadingA` and
`Literature.GrossZagier` alone (bp-hecke-fe's `certifiedRankTYZClRk_of_gaussPointCount`: only
`HeckeContinuation5`, the case `d ≡ 5 (mod 8)` squarefree, is used, and it is proved). Hence
Theorem 1.1 (`FrozenTarget`) from `SixContactMin` and these two literature Props.
-/

namespace ZInQ.Contrib.GaussFE

open ZInQ.Contrib.HeckeFE

/-- **CR₃ from TYZ reading A and Gross–Zagier.** -/
theorem certifiedRankTYZClRk_of_readingA_grossZagier (hA : ZInQ.Literature.TYZThm35ReadingA)
    (hG : ZInQ.Literature.GrossZagier) : ZInQ.RouteK.Rank.CertifiedRankTYZClRk :=
  certifiedRankTYZClRk_of_gaussPointCount hA hG gaussPointCount

/-- **Theorem 1.1 from `SixContactMin`, TYZ Theorem 3.5(2) in reading A and Gross–Zagier.** -/
theorem frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier (hH : ZInQ.SixContactMin)
    (hA : ZInQ.Literature.TYZThm35ReadingA) (hG : ZInQ.Literature.GrossZagier) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk hH
    (certifiedRankTYZClRk_of_readingA_grossZagier hA hG)

/-- **Theorem 1.1 from `SixContactMin`, the TYZ inputs I1–I7 and Gross–Zagier** (the headline
`..._tyzInputs_functionalEquation5_grossZagier` with `FunctionalEquation5` discharged). -/
theorem frozenTarget_of_sixContactMin_tyzInputs_grossZagier (hH : ZInQ.SixContactMin)
    (hT : ZInQ.PropN.TYZInputs) (hG : ZInQ.Literature.GrossZagier) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzInputs_functionalEquation5_grossZagier
    hH hT ZInQ.Contrib.functionalEquation5 hG

end ZInQ.Contrib.GaussFE
