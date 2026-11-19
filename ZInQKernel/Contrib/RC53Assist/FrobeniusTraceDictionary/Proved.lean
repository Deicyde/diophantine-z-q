import ZInQKernel.Contrib.RC53Assist.TateReduction.Comparison
import ZInQKernel.Contrib.RC53Assist.DetDegree.Reduction

/-!
# The good-reduction Frobenius trace dictionary, proved

`GoodReductionFrobeniusTraceDictionaryQ` (the reading translation F1 of the newform package)
follows from the reduction comparison of Tate modules, `tateReductionComparison`
(`ZInQKernel/Contrib/RC53Assist/TateReduction/Comparison.lean`), and the Frobenius determinant
form at `m = 1`, `frobeniusTateDetFormOne_proved`
(`ZInQKernel/Contrib/RC53Assist/DetDegree/Reduction.lean`), both proved without printed inputs.
-/

namespace ZInQ.Contrib.RC53Assist.FrobeniusTraceDictionary

/-- PROVED (Silverman V.2.3, VII.7.1). The good-reduction Frobenius trace dictionary
`GoodReductionFrobeniusTraceDictionaryQ` of `ZInQKernel/Contrib/RC53Assist/NewformPeriodsDictionary/`
(the Frobenius on the `ℓ`-adic Tate module at a prime `p ≠ ℓ` of good reduction has the trace of
the reduction's point count). -/
theorem goodReductionFrobeniusTraceDictionaryQ_proved :
    ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.GoodReductionFrobeniusTraceDictionaryQ :=
  ZInQ.Contrib.RC53Assist.TateReduction.goodReductionFrobeniusTraceDictionaryQ_of_tateDetFormOne
    ZInQ.Contrib.RC53Assist.DetDegree.frobeniusTateDetFormOne_proved

end ZInQ.Contrib.RC53Assist.FrobeniusTraceDictionary
