
/-! ## g0-assemble: wave 26 assembled — `GluePieces` from `GluePieces2`

Task g0-assemble, 2026-11-13. The ten fields of `HSyn.GluePieces` (above, unchanged) are derived
from the smaller named Props that wave 26 reduced them to, bundled as `HSyn.GluePieces2`:

| `GluePieces` field | wave-26 task | how it is obtained here |
|---|---|---|
| `dimFinite` | g0-dim | `G0Split.dimFinite` (proved, Mathlib only) |
| `dimBaseChange` | g0-dim | `G0Split.dimBaseChange` (proved, Mathlib only) |
| `fibreSimple` | g0-fibresimple | `G0FibreSimple.fibreSimple_of_leaves` from `t.t6`, `t.t27`, the textbook leaves `MulIsogeny`, `RigidityHom`, the glue `FiniteDescends` and the glue `FibreComTrivial` (blocked on qm-pin) |
| `productModelHeight` | g0-heightadd | `ZInQ.G0HeightAdd.productModelHeight_of` with `productMetrization_of_geo`, from four glue Props |
| `stableHeightBaseChange` | g0-stablebc | `G0StableBC.stableHeightBaseChange_of_hodgeLine` from the glue `HodgeLineBaseChange` |
| `productExists` | g0-product | `G0Product.productExists` (proved, Mathlib only) |
| `reverseIsogeny` | g0-reverseisog | `G0RevIsog.reverseIsogeny_of_leaves r dimFinite` (route B: R19 and H5 of the bundle) |
| `thetaPoint` | g0-thetapoint | `ThetaPt.thetaPointOfFibre_of_qm_ratios` from the glue `FibreQMPeriod` (blocked on qm-pin) and the leaf candidate `ThetaRatiosAlgebraic` |
| `modularConstituent` | g0-mod-field, g0-mod-galois, g0-mod-newform | **kept as one field**: the three ranges are not composed in one file (see `docs/research/g0-assemble.md` §3) |
| `heightCopies` | (no wave-26 task) | kept as one field (glue, pure transport) |
-/

section G0AssembleSec

noncomputable section

namespace HSyn

open G0Split

/-- **The glue Props left after wave 26** (g0-assemble). Each field is a named `def … : Prop` of a
wave-26 task, copied verbatim into this file in that task's section above; kinds as in
`docs/research/g0-assemble.md` §2 (LEAF = textbook theorem new to the bundles; GLUE = to be proved
by the project; QM-PIN = glue that cannot be proved as stated until task qm-pin repairs the QM
clauses `R1fpProps`, `R2fpProps`). -/
structure GluePieces2 : Prop where
  /-- g0-fibresimple, LEAF (textbook; Mumford §4 Application 2, Milne Thm 8.2, UNVERIFIED
  locators): `[n]` is finite and surjective for `n ≠ 0` (characteristic 0). -/
  mulIsogeny : G0FibreSimple.MulIsogeny
  /-- g0-fibresimple, LEAF (textbook; Mumford §4 Cor. 1, Milne Cor. 2.2, UNVERIFIED locators):
  rigidity, a pointed morphism of abelian varieties is a homomorphism. -/
  rigidityHom : G0FibreSimple.RigidityHom
  /-- g0-fibresimple FS1b′, GLUE (EGA IV₂ 2.7.1, UNVERIFIED): `IsFinite` descends along
  `Spec L → Spec K`. -/
  finiteDescends : G0FibreSimple.FiniteDescends
  /-- g0-fibresimple FS5, GLUE, **QM-PIN**: NoCM on the fibre, `End_𝒪(P.A) = ℤ`. -/
  fibreComTrivial : G0FibreSimple.FibreComTrivial
  /-- g0-heightadd (stated in def-faltings), GLUE: uniqueness of analytic uniformizations. -/
  analyticUniformizationUnique : ZInQ.DefFaltings.AnalyticUniformizationUnique
  /-- g0-heightadd, GLUE: two metrizations of one group model have the same dimension. -/
  metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique
  /-- g0-heightadd, GLUE: every group model has a metrization. -/
  metrizationExists : ZInQ.G0HeightAdd.MetrizationExists
  /-- g0-heightadd P2a-geo, GLUE: the product metrization with multiplicative index,
  coefficients and covolumes. -/
  productMetrizationGeo : ZInQ.G0HeightAdd.ProductMetrizationGeo
  /-- g0-stablebc, GLUE (geometric half of h5-neron's H4a): the natural map on `⋀^g ω` under base
  change of group models. -/
  hodgeLineBaseChange : G0StableBC.HodgeLineBaseChange
  /-- g0-thetapoint, GLUE, **QM-PIN**: a uniformization lattice of the fibre is a QM lattice
  `ι(𝒪)(τ,1)ᵀ` with `j_θ(Ω(τ)) = J(u)`. -/
  fibreQMPeriod : G0Split.ThetaPt.FibreQMPeriod
  /-- g0-thetapoint, LEAF candidate (composite of published results: Shimura 1976 / Mumford Tata
  II; UNVERIFIED locators): theta-constant ratios at a period matrix of an abelian surface over a
  number field are algebraic. -/
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- G2, G4, G7-G16, GLUE, kept whole (the three wave-26 ranges are not yet composed in one file;
  `KernelFieldExists` inside it is QM-PIN). -/
  modularConstituent : G0Split.ModularConstituent
  /-- leaf-adopt2's transport target, GLUE (no wave-26 task). -/
  heightCopies : HeightCopiesAgree

/-- **`GluePieces` from `GluePieces2` and the leaf bundles** (g0-assemble): every field of
`GluePieces` is a wave-26 theorem applied to fields of `GluePieces2`, `r` or `t`. -/
theorem gluePieces_of_gluePieces2 (r : ResearchLeaves) (t : TextbookLeaves) (gp2 : GluePieces2) :
    GluePieces where
  dimFinite := G0Split.dimFinite
  dimBaseChange := G0Split.dimBaseChange
  fibreSimple := G0FibreSimple.fibreSimple_of_leaves t gp2.mulIsogeny gp2.rigidityHom
    ⟨gp2.finiteDescends, gp2.fibreComTrivial⟩
  productModelHeight := ZInQ.G0HeightAdd.productModelHeight_of gp2.analyticUniformizationUnique
    gp2.metrizationDimUnique gp2.metrizationExists
    (ZInQ.G0HeightAdd.productMetrization_of_geo gp2.productMetrizationGeo)
  stableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine gp2.hodgeLineBaseChange
  productExists := G0Product.productExists
  reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves r G0Split.dimFinite
  thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios gp2.fibreQMPeriod
    gp2.thetaRatiosAlgebraic
  modularConstituent := gp2.modularConstituent
  heightCopies := gp2.heightCopies

/-- **G0 after wave 26** (g0-assemble): the leaf bundles and `GluePieces2` imply
`ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves2 (r : ResearchLeaves) (t : TextbookLeaves) (gp2 : GluePieces2) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leaves r t (gluePieces_of_gluePieces2 r t gp2)

end HSyn

end

end G0AssembleSec

#print axioms HSyn.gluePieces_of_gluePieces2
#print axioms HSyn.sixContactMin_of_leaves2
