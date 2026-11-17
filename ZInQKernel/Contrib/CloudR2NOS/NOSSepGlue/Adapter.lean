import ZInQKernel.Contrib.OneProof.NeronOggShafarevich
import ZInQKernel.Contrib.CloudR2NOS.NOSSepGlue.Glue

/-! H5 lane3 adapter (2026-11-17, SOURCE-ONLY): the owner's `NOSProof.NOSConverseSep` (e9828e92, staged
byte-exact) is proved by `nosConverseSep_proof`; elaboration checks the statement match by defeq. -/
example : NOSProof.NOSConverseSep := ZInQ.Contrib.CloudR2NOS.NOSSepGlue.nosConverseSep_proof
