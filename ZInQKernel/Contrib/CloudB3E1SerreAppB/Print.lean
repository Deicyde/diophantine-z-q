import ZInQKernel.Contrib.CloudB3E1SerreAppB.ConcreteLocal
import ZInQKernel.Contrib.CloudB3E2Conrad.ConradB3Stage2

/-!
# The consumer's `ConradAppBPrint` from Serre's statement at the Artin map of `K`

Step C8 (diophantine_zq.tex, sec:height, L760–764). The consumer field `conradAppBPrint`
(`ConradAppBPrint = ConradNearOnePrint ∧ ConradB3Print`, ConradB3Verbatim) follows from the
single named input `LocalArtin.serreA6OnIntegerUnits`. That is Serre, *Abelian `l`-adic
representations and elliptic curves*, Addison-Wesley 1989, III-44 (A5, Theorem 2 (ii)) ⇔
III-49/50 (A6, Proposition 6 (iv)), with (iv) on an open subgroup of `U_K` and at the local
Artin map of `K`.

* Near-one half: `conradNearOne_of_serre`, then the reading of the display on the
  abelianization (`artinNearOnePrint_iff`).
* B.3 half: `conradIdentityWeight_of_serreIntegerUnits`, then the stage-2 lemma
  `CloudB3E2.conradB3Print_of_identityWeight`. That lemma turns the identity line into the
  full constant-weight splitting over `G_{ℚ_p}`, using Tate's theorems already proved in the
  tree.

Kind: proved from the named input `serreA6OnIntegerUnits` (PRINT, pending independent source
review). Conrad's preprint serves only as the skeleton.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.SerreAppB

open HDec.G0Galois.C8Conrad.Bridges

/-- The near-one display, read on the abelianization. Kind: proved. -/
theorem conradNearOnePrint_of_nearOne (h : ConradNearOne) : ConradNearOnePrint := by
  intro p _ K _ _ ψ i hc hHT
  obtain ⟨n, hn⟩ := h p K ψ i hc hHT
  exact ⟨n, (artinNearOnePrint_iff p ψ hc n).mpr hn⟩

/-- **C8, the consumer's `ConradAppBPrint` from Serre's statement at Artin_K.** Kind: proved
from the named input `LocalArtin.serreA6OnIntegerUnits`. -/
theorem conradAppBPrint_of_serreIntegerUnits (h : LocalArtin.serreA6OnIntegerUnits) :
    ConradAppBPrint :=
  ⟨conradNearOnePrint_of_nearOne
      (conradNearOne_of_serre (LocalArtin.serreA6Print_of_integerUnits h)),
    CloudB3E2.conradB3Print_of_identityWeight (conradIdentityWeight_of_serreIntegerUnits h)⟩

/-- The same, from `SerreA6Print` (which carries the GLUE norm reading). Kind: proved from
the named input `SerreA6Print`. -/
theorem conradAppBPrint_of_serre (h : SerreA6Print) : ConradAppBPrint :=
  ⟨conradNearOnePrint_of_nearOne (conradNearOne_of_serre h),
    CloudB3E2.conradB3Print_of_identityWeight (conradIdentityWeight_of_serre h)⟩

end HDec.G0Galois.C8Conrad.SerreAppB
