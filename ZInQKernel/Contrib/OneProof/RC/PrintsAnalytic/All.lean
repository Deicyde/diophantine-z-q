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
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.TwistedFEKronecker
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.TwistedFEFricke
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.TwistedFE

/-!
# Lane RC8: the analytic printed theorems of the proof of Theorem 5.3

Umbrella module. The printed leaves (PRINT) and textbook facts (GLUE) of this lane, all stated over
the shared vocabulary `ZInQ.Contrib.CloudB3RC53` (`qtwist`, `IsLContinuation`, `AnalyticRank`,
`completedL`, `RootNumber`) and, for the literal prints, over the vendored genuine newforms:

* PRINT: `HoffsteinLuoTheorem`, `BFHTheorem` (literal, over newforms);
  `HoffsteinLuoCurve`, `TwistedRootNumberCurve`, `BFHCurve` (curve forms, PROVED from the literal
  ones in `Bridges.lean`); `DesjardinsRootNumberFilter` (global-consequence form);
  `WaldspurgerCor2`, `WaldspurgerNonvanishing` (print not read; the latter includes Elliot's local
  construction, with its conclusion that the scalar character has two-power order, App E
  L7918–7919, L7943–7944); `ModularNewform` (BCDT Theorem A condition (2), Milne Theorem 11.19 /
  Proposition 11.21).
* GLUE: `HasseConvergence`, `TwistDictionary` (the latter PROVED as `twistDictionary`,
  `TwistDictionary/Dictionary.lean`).
* PROVED: `TwistedFunctionalEquation` (literal, over newforms; lane RC33's
  `twistedFunctionalEquation_proved`, `TwistedFE.lean`, from the primitive quadratic character
  `χ_D` of `TwistedFEKronecker.lean` and the Fricke relation of the twist of
  `TwistedFEFricke.lean`).
* Dokchitser–Dokchitser Theorem 1.8, BCDT Theorem A and Cai–Shu–Tian Theorem 1.1 are the shared
  blueprint's leaves and Kolyvagin Theorem 1 its cited statement (GLUE), all in
  `ZInQ.Contrib.CloudB3RC53.Prints`; they are not restated.
-/
