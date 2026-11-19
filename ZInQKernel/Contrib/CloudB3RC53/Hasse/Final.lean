import ZInQKernel.Contrib.CloudB3RC53.Hasse.Convergence
import ZInQKernel.Contrib.CloudB3RC53.WeilIsogeny.HasseProof
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.ArtinUnconditional

/-!
# `HasseConvergence` and `ArtinFactorization`, proved

The statement `HasseBound` (not a print; Silverman V.1.1 as a reference only) is proved in
`WeilIsogeny/HasseProof.lean` (`hasseBoundProved_proof`, same statement), so `HasseConvergence`
holds outright (`hasseConvergence_proved`), and `ArtinFactorization` needs only `ModularNewform`
(`artinFactorization_unconditional`, from `artinFactorization_of_newform'`), and (3.4) follows from
the printed leaves and `ModularNewform` (`genusLower34_unconditional`).

Classification: PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.Hasse

/-- **`HasseConvergence`, proved** (absolute convergence of `L(E, s)` on `Re s > 3/2`). -/
theorem hasseConvergence_proved : ZInQ.Manuscript.RC.PrintsAnalytic.HasseConvergence :=
  hasseConvergence_proof (fun F _ _ W _ => WeilIsogeny.hasseBoundProved_proof F W)

/-- **`ArtinFactorization` from `ModularNewform` alone.** -/
theorem artinFactorization_unconditional (hMN : ZInQ.Manuscript.RC.PrintsAnalytic.ModularNewform) :
    ZInQ.Contrib.CloudB3RC53.GenusOdd.ArtinFactorization :=
  ZInQ.Contrib.CloudB3RC53.GenusOdd.artinFactorization_of_newform' hasseConvergence_proved hMN

/-- **(3.4) from the printed leaves and `ModularNewform`.** -/
theorem genusLower34_unconditional (P : ZInQ.Contrib.CloudB3RC53.Prints)
    (hMN : ZInQ.Manuscript.RC.PrintsAnalytic.ModularNewform) :
    ZInQ.Contrib.CloudB3RC53.GenusOdd.GenusLower34 :=
  ZInQ.Contrib.CloudB3RC53.GenusOdd.genusLower34_of_newform' P hasseConvergence_proved hMN

end ZInQ.Contrib.CloudB3RC53.Hasse
