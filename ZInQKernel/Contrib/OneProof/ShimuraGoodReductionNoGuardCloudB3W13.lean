import ZInQKernel.OneProof.H.TailW
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D8.FinalProofCandidate

/-!
# Guard-free Shimura good reduction: Cloud Batch 3 Worker 13

This wrapper has exactly the original H-119 type and no theorem parameters.
It reuses the recovered fine-moduli factory and the genuine object/family
converse dictionaries. No existing statement or module is modified.

This is a source checkpoint, not yet a verified discharge. On a main generation
that carries `SGRSplit.ShimuraIntegralModelRep`, an unconditional H-119 proof can
replace the conditional assignment at the old consumer in an integrator re-fold.
It is not itself a proof of the stronger all-base representability statement, nor
of the general `SGRDirect.NVLocalInertia` assertion.
-/

namespace ZInQ.Contrib.CloudB3W13

/-- The exact original guard-free Shimura good-reduction statement. -/
theorem shimuraGoodReductionNoGuard_proof :
    HDec.CurveSplitGR.ShimuraGoodReductionNoGuard :=
  ZInQ.Contrib.CloudB2Shimura.Dictionary.D8.shimuraGoodReductionNoGuard_proof

end ZInQ.Contrib.CloudB3W13
