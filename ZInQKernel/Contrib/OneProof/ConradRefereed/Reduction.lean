import ZInQKernel.Contrib.OneProof.ConradRefereed.LocalArtin
import ZInQKernel.Contrib.OneProof.ConradRefereed.NearOne

/-! Reduce the exact C8 row to the one printed Serre equivalence. -/

namespace HDec.G0Galois.C8Conrad

/-- The C8 row follows from Serre's Ch. III Appendix A6 equivalence (locator UNVERIFIED),
with the norm and Hodge–Tate comparisons proved separately. -/
theorem conradAppB_of_refereed (h : SerreAppB.LocalArtin.SerreA6Prop6) : ConradAppB :=
  let hnorm := SerreAppB.LocalArtin.serreA6NormEquivalence_of_prop6 h
  ⟨Bridges.conradAppBQp_of_nearOne (SerreAppB.conradNearOne_of_serre hnorm),
   Bridges.conradPropB3Qp_of_identityWeight (SerreAppB.conradIdentityWeight_of_serre hnorm)⟩

#print axioms conradAppB_of_refereed

end HDec.G0Galois.C8Conrad
