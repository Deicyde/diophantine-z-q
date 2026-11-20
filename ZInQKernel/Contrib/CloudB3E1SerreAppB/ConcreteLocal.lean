import ZInQKernel.Contrib.CloudB3E1SerreAppB.Concrete
import ZInQKernel.Contrib.CloudB3E1SerreAppB.LocalArtin

/-!
# Conrad's Appendix B (concrete form) from Serre's statement at the Artin map of `K`

Step C8 (diophantine_zq.tex, sec:height, L760–764). The single named input is
`LocalArtin.serreA6OnIntegerUnits`. That is Serre, *Abelian `l`-adic representations and elliptic
curves*, Addison-Wesley 1989, III-44 (A5, Theorem 2 (ii)) ⇔ III-49/50 (A6, Proposition 6 (iv)),
specialized to ground field = coefficient field = a finite Galois `K/ℚ_p`, with (iv) on an open
subgroup of `U_K` and at the local Artin map of `K`. The norm-functoriality reading used by
`SerreA6Print` is proved (`LocalArtin.serreA6Print_of_integerUnits`, via Tau Ceti's
`artinMap_norm`), so no GLUE remains on this route. Conrad's preprint serves only as the
skeleton.

Kind: proved from the named input `serreA6OnIntegerUnits` (PRINT, pending independent source
review).
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.SerreAppB

open HDec.G0Galois.C8Conrad.Bridges

/-- **C8, `ConradAppBConcrete` from Serre's statement at Artin_K.** Kind: proved from the
named input `LocalArtin.serreA6OnIntegerUnits`. -/
theorem conradAppBConcrete_of_serreIntegerUnits (h : LocalArtin.serreA6OnIntegerUnits) :
    ConradAppBConcrete :=
  conradAppBConcrete_of_serre (LocalArtin.serreA6Print_of_integerUnits h)

/-- **C8, `ConradAppB` from Serre's statement at Artin_K**, via the existing
`conradAppB_of_concrete`. Kind: proved from the named input
`LocalArtin.serreA6OnIntegerUnits`. -/
theorem conradAppB_of_serreIntegerUnits (h : LocalArtin.serreA6OnIntegerUnits) :
    ConradAppB :=
  conradAppB_of_serre (LocalArtin.serreA6Print_of_integerUnits h)

/-- **C8, Conrad B.3 identity line from Serre's statement at Artin_K.** Kind: proved from
the named input `LocalArtin.serreA6OnIntegerUnits`. -/
theorem conradIdentityWeight_of_serreIntegerUnits (h : LocalArtin.serreA6OnIntegerUnits) :
    ConradIdentityWeight :=
  conradIdentityWeight_of_serre (LocalArtin.serreA6Print_of_integerUnits h)

end HDec.G0Galois.C8Conrad.SerreAppB
