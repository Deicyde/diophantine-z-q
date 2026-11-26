import ZInQKernel.Contrib.OneProof.C8DeRham.ActualBdRRowsOfDeRham
import ZInQKernel.Contrib.OneProof.C8DeRham.TraceBurnsideTwist
import ZInQKernel.Contrib.OneProof.C8DeRham.ConradReceiver
import ZInQKernel.Contrib.OneProof.C8DeRhamTransport.Local

/-! # Checked comparison lemmas for the manuscript-order C8 receiver -/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

/-- Extending the finite coefficient model preserves the same de Rham rank. -/
theorem deRhamExtends_proof : DeRhamExtends := by
  intro p _ E F _ _ h n r hdr
  exact _root_.ZInQ.Contrib.G9.C8DeRhamTransport.isDeRham_extend p h r hdr

/-- Period rows of the original coefficient matrices are a consequence of the
actual de Rham rank, not an additional input from the literature. -/
theorem deRhamHasRows_proof : DeRhamHasRows := by
  intro p _ E _ _ n r hdr
  exact hasBdRRows_of_isDeRham p E r hdr

/-- Transfer the original irreducibility across equality of traces, then use
the proved matrix Brauer–Nesbitt result. The Kato witness is not assumed
semisimple. -/
theorem conjOfTraceIrredFive_proof : ConjOfTraceIrredFive := by
  intro r ρ hirr htr
  exact isConj_of_trace_eq_of_burnside r ρ hirr htr

end HDec.G0Galois.C8Conrad.Manuscript
