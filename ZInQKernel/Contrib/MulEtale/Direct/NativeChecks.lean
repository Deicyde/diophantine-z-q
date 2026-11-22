import ZInQKernel.Contrib.MulEtale.Direct.AllBase
import ZInQKernel.Contrib.MulEtale.Expected
import ZInQKernel.Contrib.OneProof.H.TailQ

/-!
# Native H-101 target and T4 consumer checks

These are applications of the actual full arbitrary-base multiplication proof
to the unchanged native target and consumer. No conditional supplier premise is
introduced into the new multiplication theorem or these two closed proofs.
-/

namespace H101DirectFieldRoute.NativeChecks

example : ZInQ.Contrib.MulEtale.Expected.target = AvSplit.T4.MulEtaleAbelianScheme := rfl

/-- Supply precisely the native H-101 proposition. -/
theorem mulEtale : AvSplit.T4.MulEtaleAbelianScheme :=
  H101DirectFieldRoute.multiplication_etale

/-- Invoke the original consumer with the supplied native proposition. -/
theorem reductionTorsionBijective : PkgI2.ReductionTorsionBijective.{0} :=
  AvSplit.T4.reductionTorsionBijective_of_mulEtale mulEtale

#print axioms H101DirectFieldRoute.multiplication_etale
#print axioms mulEtale
#print axioms reductionTorsionBijective

end H101DirectFieldRoute.NativeChecks
