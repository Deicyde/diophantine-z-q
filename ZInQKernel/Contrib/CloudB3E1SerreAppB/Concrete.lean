import ZInQKernel.Contrib.CloudB3E1SerreAppB.NearOne

/-!
# Conrad's Appendix B (concrete form) reduced to Serre's Appendix to Chapter III

Step C8 (diophantine_zq.tex, sec:height, L760–764). The tree's `ConradAppBConcrete` is the
conjunction of the near-one display and the identity-line form of Proposition B.3. Both now
follow from the single named input `SerreA6Print`:

* Serre, *Abelian `l`-adic representations*, 1989 ed., III-44 (A5, Theorem 2 (ii)) ⇔
  III-49/50 (A6, Proposition 6 (iv)), printed;
* (iv) read through norm functoriality of local class field theory (Serre III-5; Tau Ceti
  `artinMap_norm` for local-field types), GLUE.

Through the existing bridge `conradAppB_of_concrete`, this also discharges the C8 field
`ConradAppB`. Conrad's preprint is not used as an input; it serves only as the skeleton.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.SerreAppB

open HDec.G0Galois.C8Conrad.Bridges

/-- **C8, `ConradAppBConcrete` from Serre.** Kind: proved from the named input
`SerreA6Print` (PRINT + GLUE). -/
theorem conradAppBConcrete_of_serre (h : SerreA6Print) : ConradAppBConcrete :=
  ⟨conradNearOne_of_serre h, conradIdentityWeight_of_serre h⟩

/-- **C8, `ConradAppB` from Serre**, via the existing `conradAppB_of_concrete`.
Kind: proved from the named input `SerreA6Print` (PRINT + GLUE). -/
theorem conradAppB_of_serre (h : SerreA6Print) : ConradAppB :=
  conradAppB_of_concrete (conradAppBConcrete_of_serre h)

end HDec.G0Galois.C8Conrad.SerreAppB
