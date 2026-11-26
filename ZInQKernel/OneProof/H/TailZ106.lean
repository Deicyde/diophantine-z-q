import ZInQKernel.OneProof.H.TailZ105
import ZInQKernel.Contrib.OneProof.VpDualMerge.Chain
import ZInQKernel.Contrib.OneProof.TatePrints.Glue

/-! # OneProof H, tate-prints-fold: `sixContactMin_of_open99`

Fields removed (replaced by single prints, not proved): `scholzeH1AbVar`, `t10TateDuality`. The chain reads
them only through `DeRhamScholze.HTMerge.VpDualDeRhamAbVar`, the one field `vpDual` of vpdual-merge's copy chain
(`Contrib/OneProof/VpDualMerge/Chain.lean`, top `sixContactMin_of_open98_vp`), and
`DeRhamScholze.TatePrints.vpDual_of_colmezFontaine` (`Contrib/OneProof/TatePrints/Glue.lean`, #213) derives it
from the two new leaves.
Fields added (new leaves): `colmez1992DeRhamAbVar`, `fontaine1982HTAbVar`. -/

namespace HDec

namespace HSyn

/-- `OpenAddedLeaves29` without `scholzeH1AbVar`, `t10TateDuality`, with the leaves `colmez1992DeRhamAbVar`,
`fontaine1982HTAbVar` (tate-prints-fold). -/
structure OpenAddedLeaves30 : Prop where
  /-- Colmez, Périodes p-adiques des variétés abéliennes, Math. Ann. 292 (1992), 629-644, Théorème 5.2 (i)-(ii),
  p. 639: for an abelian variety A over a finite extension F of ℚ_p, the p-adic period pairing (ω, u) ↦ ∫_u ω
  takes values in B_dR⁺, commutes with the action of G_F, and is non-degenerate on the side of
  V_p(A) = ℚ_p ⊗ T_p(A) after extending scalars to B_dR. H¹_dR(A) is weakened to an existential type;
  bilinearity in ω, the Fil¹ clause and (iii) are dropped. -/
  colmez1992DeRhamAbVar : _root_.DeRhamScholze.TatePrints.Colmez1992DeRhamAbVar
  /-- Fontaine, Formes différentielles et modules de Tate des variétés abéliennes sur les corps locaux,
  Invent. Math. 65 (1982), 379-409, Théorème 2 (Tate, Raynaud), p. 388, in dimension form: for an abelian
  variety A of dimension g over a finite extension F of ℚ_p, Hom_{G_F}(V_p(A), ℂ_p(1)) and
  Hom_{G_F}(V_p(A), ℂ_p) both have dimension g over F (`htF (A.galRep p) i`, i = 1, 0). The equality with g is
  printed in the proof on p. 388 ("chacune de ces dimensions est égale à d"); the maps ρ¹_X, ρ⁰_X are dropped. -/
  fontaine1982HTAbVar : _root_.DeRhamScholze.TatePrints.Fontaine1982HTAbVar

/-- `OpenAddedLeaves29VP` from `OpenAddedLeaves30`: `vpDual` from the two leaves by
`vpDual_of_colmezFontaine`. -/
theorem openAddedLeaves29VP_of_OpenAddedLeaves30 (n : OpenAddedLeaves30) : OpenAddedLeaves29VP where
  vpDual := _root_.DeRhamScholze.TatePrints.vpDual_of_colmezFontaine n.colmez1992DeRhamAbVar
    n.fontaine1982HTAbVar

/-- **G0 with only the open leaves and the open glue** (tate-prints-fold). -/
theorem sixContactMin_of_open99 (r : OpenResearchLeaves78) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves30) :
    ZInQ.SixContactMin :=
  sixContactMin_of_open98_vp r t (openAddedLeaves29VP_of_OpenAddedLeaves30 l)

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open99
