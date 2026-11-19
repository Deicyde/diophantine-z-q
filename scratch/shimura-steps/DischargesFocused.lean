import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.ShimuraSteps

/-! One-row harness for the stock command. The binder has exactly the type of
the projected field in TailZ87; the `True` codomain is just the terminator for
the scan. This file does not import the full assembly or check its other rows. -/
def ZInQ.OneProof.frozenTarget : (shimuraThm1Af : R16Thm1b.ShimuraThm1Af) → True :=
  fun _ => trivial

#discharges
