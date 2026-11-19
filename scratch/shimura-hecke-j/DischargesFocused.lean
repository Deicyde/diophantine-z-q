import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.SameDimFinite
import ZInQKernel.Contrib.OneProof.ShimuraHeckeJ

/-! Stock command with the quotient row type from the assembly and no other rows. -/

theorem ZInQ.OneProof.frozenTarget : (shimuraThm1Af : R16Thm1b.ShimuraThm1Af) → True :=
  fun _ => trivial

example (hH : ShimuraSteps.ShimuraHeckeRelations) :
    ShimuraSteps.ShimuraThm1AsPrinted → R16Thm1b.ShimuraThm1Af :=
  fun hP => ShimuraSteps.shimuraThm1Af_of_printed' hP hH

#discharges
