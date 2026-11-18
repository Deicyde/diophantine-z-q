import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.C8Conrad
import ZInQKernel.Contrib.OneProof.C8LocAlg
import ZInQKernel.Contrib.OneProof.C8CFT
import ZInQKernel.Contrib.OneProof.C8ConradB
import ZInQKernel.Contrib.OneProof.C8Poincare
import ZInQKernel.Contrib.OneProof.C8Ladic
import ZInQKernel.Contrib.OneProof.C8Dicts
import ZInQKernel.Contrib.OneProof.C8Twist
import ZInQKernel.Contrib.OneProof.C8Printed

#discharges

#print axioms HDec.G0Galois.C8Conrad.isLocallyAlgebraic_iff_conrad
#print axioms HDec.G0Galois.C8Conrad.htMult_eq_conradHTMult_neg
#print axioms HDec.G0Galois.C8Conrad.locAlgExponentEqWeight_of_conradPropB3
#print axioms HDec.G0Galois.C8Conrad.locAlgExponentEqWeight_of_conradAppB
#print axioms HDec.G0Galois.C8Conrad.c8TwistFinite_of_conradB
#print axioms HDec.G0Galois.C8Conrad.g12DetPZ_of_inputs
#print axioms HDec.G0Galois.C8Conrad.c8Inputs_of_leaves
#print axioms HDec.G0Galois.C8Conrad.c8TwistFinite_of_printed
#print axioms HDec.G0Galois.C8Conrad.g12DetPZ_of_printed

/-- The sign chain, checked: Conrad's exponent of the project's exponent `n` is `-n`, and the project's multiplicity of the
weight `w` is Conrad's multiplicity of `-w` over `[E:ℚ_p]`. -/
example (p : ℕ) [Fact p.Prime] (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ψ : PkgI4.GQp p →* Eˣ) (n : ℤ) :
    HDec.G0Galois.C8Conrad.IsLocallyAlgebraic p ψ n ↔ HDec.G0Galois.C8Conrad.IsLocallyAlgebraicConrad p ψ (-n) :=
  HDec.G0Galois.C8Conrad.isLocallyAlgebraic_iff_conrad p ψ n
