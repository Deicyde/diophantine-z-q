import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.SameDimFinite

/-! One-row harness for the stock command, using the type of the projected
`shimuraThm1Af` field in `TailZ87.lean`. -/
theorem ZInQ.OneProof.frozenTarget : (shimuraThm1Af : R16Thm1b.ShimuraThm1Af) → True :=
  fun _ => trivial

#discharges
