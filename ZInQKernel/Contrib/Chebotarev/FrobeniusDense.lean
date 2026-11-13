import ZInQKernel.Contrib.Chebotarev.Exists
import ZInQKernel.Contrib.Chebotarev.FrobeniusDenseOfExists

/-!
# Leaf T18 (`HSyn.FrobeniusDense`), proved

`ZInQ.Contrib.ChebFD.HSyn.FrobeniusDense` is `HSyn.FrobeniusDense` of
`scratch/h-decomposition/Leaves.lean`, restated verbatim (with the `HSyn` definitions it uses) in
`ZInQKernel/Contrib/Chebotarev/FrobeniusDenseOfExists.lean`.  That file reduces it to the finite
form `PkgI6.ChebotarevExists` (the proof of task t-skolem-kw); `ZInQ.Contrib.chebotarevExists`
(`ZInQKernel/Contrib/Chebotarev/Exists.lean`, from Tau Ceti's Chebotarev density theorem) proves
the finite form.

## Main result

* `ZInQ.Contrib.frobeniusDense : ZInQ.Contrib.ChebFD.HSyn.FrobeniusDense`

No `sorry`, no `axiom`.
-/

namespace ZInQ.Contrib

/-- **Leaf T18 (Frobenius elements outside any finite set of primes are dense in `G_ℚ`),
proved.** -/
theorem frobeniusDense : ChebFD.HSyn.FrobeniusDense :=
  ChebFD.HSyn.frobeniusDense_of_chebotarev chebotarevExists

end ZInQ.Contrib
