import ZInQKernel.OneProof.H.TailS
import ZInQKernel.Contrib.CloudB3W11AxCompletion.AxSenTateBridge
import ZInQKernel.Contrib.CloudB3W11AxEstimate.AxApprox

/-!
# Ax–Sen–Tate over the exact OneProof definitions

The uniform algebraic estimate is ported from Anthropic's public FLT snapshot
`6e837e75355538c7f80bab5b956861e86c4eacc2` (Apache-2.0). Its constant is `p²`,
independent of the algebraic approximant's degree. The completion and finite-field
closed-image steps use Mathlib and the repository's genuine action `cpAct`.
See the supporting modules' LICENSE/NOTICE files for the preserved source notices.

The theorem below has the exact existing `HodgeSplit.AxSenTate` type, with no
unproved arithmetic hypotheses and no changes to the statement or definitions.
-/

namespace ZInQ.Contrib.CloudB3W11

/-- Tate 1967, §3.3, Theorem 1, finite-extension specialization: a `G_K`-fixed
point of the genuine `ℂ_p` completion is an element of `K`. -/
theorem axSenTate_proof : ZInQ.Contrib.HodgeSplit.AxSenTate := by
  apply ZInQ.Contrib.CloudB3W11AxCompletion.axSenTate_of_uniformAxEstimates
  intro p hp K hK
  refine ⟨(p : ℝ) ^ 2, by positivity, ?_⟩
  intro a δ hδ h
  exact ZInQ.Contrib.CloudB3W11AxEstimate.uniform_ax_approximation p K a δ hδ h

end ZInQ.Contrib.CloudB3W11
