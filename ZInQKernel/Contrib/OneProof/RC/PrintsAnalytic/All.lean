import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Basic
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Newform
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Parity
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.HoffsteinLuo
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.BFH
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Desjardins
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Waldspurger
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Bridges
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Milne
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Uses

/-!
# Lane RC8: the analytic printed theorems of the proof of Theorem 5.3

Umbrella module. The printed leaves (PRINT) and textbook facts (GLUE) of this lane, all stated over
the shared vocabulary `ZInQ.Contrib.CloudB3RC53` (`qtwist`, `IsLContinuation`, `AnalyticRank`,
`completedL`, `RootNumber`) and, for the literal prints, over the vendored genuine newforms:

* PRINT: `HoffsteinLuoTheorem`, `TwistedFunctionalEquation`, `BFHTheorem` (literal, over newforms);
  `HoffsteinLuoCurve`, `TwistedRootNumberCurve`, `BFHCurve` (curve forms, PROVED from the literal
  ones in `Bridges.lean`); `DesjardinsRootNumberFilter` (global-consequence form);
  `WaldspurgerCor2`, `WaldspurgerNonvanishing` (print not read); `ModularNewform` (BCDT Theorem A
  condition (2), Milne Theorem 11.19 / Proposition 11.21).
* GLUE: `HasseConvergence`, `TwistDictionary`.
* Dokchitser–Dokchitser Theorem 1.8, BCDT Theorem A, Kolyvagin Theorem 1 and Cai–Shu–Tian
  Theorem 1.1 are the shared blueprint's leaves (`ZInQ.Contrib.CloudB3RC53.Prints`) and are not
  restated.
-/
