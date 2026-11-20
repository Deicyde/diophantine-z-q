import ZInQKernel.Contrib.CloudR2CM.SerreTate.NOSAdapterProof
import ZInQKernel.Contrib.CloudR2NOS.NOSSepGlue.Adapter

/-!
# P3: good reduction at every finite place, unconditional

`P3GoodReduction` from the conditional `p3GoodReduction_of_converse` and the converse of the
criterion of Néron–Ogg–Shafarevich, `ZInQ.Contrib.CloudR2NOS.NOSSepGlue.nosConverseSep_proof`.
`NOSSepGlue.Adapter` checks, by definitional equality, that its statement is the owner's
`NOSProof.NOSConverseSep`. The converse is local: it has no Néron-model-existence premise.
-/

set_option autoImplicit false

namespace HDec.CMSerreTate

/-- **P3, proved**: good reduction at each finite place, from the converse of the criterion. -/
theorem p3GoodReduction_proved : P3GoodReduction :=
  p3GoodReduction_of_converse ZInQ.Contrib.CloudR2NOS.NOSSepGlue.nosConverseSep_proof

end HDec.CMSerreTate
