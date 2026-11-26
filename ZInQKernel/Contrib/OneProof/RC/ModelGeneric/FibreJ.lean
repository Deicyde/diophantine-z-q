import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.DetectorFibre
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.QuotientBaseChange

/-! # The first j-coordinate on the detector-independent fibre -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric

open ModelTorsion
open scoped TensorProduct

open private detectorLevel_isUnit from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels2.DetectorCyclicLevel
open private detectorCoverAlgebra detectorCoverTower from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0Level
open private rationalLevel_isUnit from
  ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N]
  (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
/-- The comparison for each admissible detector preserves the actual j-coordinate,
so all detector fibres have the same map to the rational affine j-line. -/
theorem Y0RationalBaseChange_j :
    Y0RationalBaseChange h₅ htame h₂ (detectorFibreJ h₅ htame h₂) = Y0RationalJ h₂ := by
  obtain _ | _ | n := N
  · omega
  · omega
  let R := LocalIntegers ell
  let hn := detectorLevel_isUnit h₅ htame
  let hQ := rationalLevel_isUnit (N := n + 2)
  letI := detectorCoverAlgebra h₅ htame
  letI := detectorCoverTower h₅ htame
  apply Subtype.ext
  apply Subtype.ext
  change shortCoverBaseChange hn hQ ((1 : ℚ) ⊗ₜ[R]
    algebraMap (ShortBase R) _ (shortFamily R).j) =
      algebraMap (ShortBase ℚ) _ (shortFamily ℚ).j
  exact shortCoverBaseChange_j hn hQ

#print axioms Y0RationalBaseChange_j

end WeierstrassCurve.ModelLevels.ModelGeneric
