import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalClauses
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LevelGood

/-!
# GenusOdd: the Artin factorization and (3.4) with the reduction hypothesis discharged

With `GoodReductionOffLevel` proved from the printed leaf `ModularNewform`
(`goodReductionOffLevel_of_modularNewform`), the Artin factorization of the ring-class
`L`-function needs only `HasseConvergence` (Hasse's bound), `ModularNewform` (PRINT, BCDT) and the
inert clause `LocalFactorInert` (Frobenius characteristic polynomial). Since then `HasseConvergence`
is proved and the inert clause is not needed (`ArtinUnconditional.lean`), so `ArtinFactorization`
needs only `ModularNewform` (`artinFactorization_unconditional`, `Hasse/Final.lean`).
-/

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.RC.PrintsAnalytic

/-- **`ArtinFactorization` from `HasseConvergence`, `ModularNewform` and `LocalFactorInert`**
(PROVED reduction). -/
theorem artinFactorization_of_newform (hH : HasseConvergence) (hMN : ModularNewform)
    (h : LocalFactorInert) : ArtinFactorization :=
  artinFactorization_of_inert hH (goodReductionOffLevel_of_modularNewform hMN) h

/-- **(3.4) from the printed leaves, `HasseConvergence`, `ModularNewform` and `LocalFactorInert`**
(PROVED reduction). -/
theorem genusLower34_of_newform (P : Prints) (hH : HasseConvergence) (hMN : ModularNewform)
    (h : LocalFactorInert) : GenusLower34 :=
  genusLower34_of_inert P hH (goodReductionOffLevel_of_modularNewform hMN) h

end ZInQ.Contrib.CloudB3RC53.GenusOdd
