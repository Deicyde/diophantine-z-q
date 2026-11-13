/-! # linked-frob: `LinkedFrob` from the frob chain, and `GluePieces4`

`GluePieces4` is linked-tate's `GluePieces3` (scratch/linked-tate/parts/99_bundle3.lean; all fields
copied verbatim with their docstrings) with the field `linkedFrob` replaced by frob-pieces'
`AbVarSpreadsOut` (neron-lg's N1-g1) and `ProperSmoothGenConnected`; I2-NMP and I2-Red are the
textbook leaves `t.t3`, `t.t4` of the bundle. -/

section LinkedFrobBundleSec

noncomputable section

namespace LinkedFrobRed

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

/-- **`LinkedFrob` from alg-frob-red's five inputs (proved).** -/
theorem linkedFrob_of_gen (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    UnramTate.LinkedFrob :=
  linkedFrob_of_algFrobRed (algFrobRed_of_gen hG hS hRed hE hA)

/-- **`LinkedFrob` from `GoodRedCofinite`, I2-Red and I2-NMP (proved;** frob-pieces' and
afr-absfrob's discharge of `SmoothGeomConnIntegral`, `FExtendGen`, `AbsFrob`). -/
theorem linkedFrob_of_goodRed_nmp (hG : GoodRedCofinite)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    UnramTate.LinkedFrob :=
  linkedFrob_of_algFrobRed (FrobPiecesGood.algFrobRed_of_goodRed_nmp hG hRed hN)

/-- **`LinkedFrob` from N1-g1 `AbVarSpreadsOut`, `ProperSmoothGenConnected`, I2-Red and I2-NMP
(proved).** -/
theorem linkedFrob_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    UnramTate.LinkedFrob :=
  linkedFrob_of_algFrobRed (FrobPiecesGood.algFrobRed_of_neron_nmp hsp hc hRed hN)

/-- **`LinkedFrob` from the textbook bundle, N1-g1 and `ProperSmoothGenConnected` (proved):**
I2-Red and I2-NMP are the bundle's fields `t4`, `t3`. -/
theorem linkedFrob_of_textbook (t : HSyn.TextbookLeaves) (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected) : UnramTate.LinkedFrob :=
  linkedFrob_of_neron_nmp hsp hc t.t4 t.t3

end LinkedFrobRed

namespace HSyn

open G0Split

structure GluePieces4 : Prop where
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
  /-- g0-mod-field G2, GLUE (Prop. TS + Lemma NV on the actual fibre): a separable `f`,
  `deg f ≤ 324`, whose splitting field is unramified outside `T` and carries a rational fibre. -/
  fibreCoverExists : G0ModField.FibreCoverExists
  /-- g0-mod-field G4 + B1, GLUE, **QM-PIN**: the kernel field and the conjugacy data. -/
  kernelFieldExists : G0ModField.KernelFieldExists
  /-- g0-mod-field, GLUE (STANDARD, Neukirch I §8, UNVERIFIED): a compositum of finite Galois
  extensions of `ℚ` unramified at `p` is unramified at `p`. -/
  unramifiedSup : G0ModField.UnramifiedSup
  /-- g0-mod-galois, LEAF (textbook; Burnside, Lang *Algebra* XVII §3, UNVERIFIED locator). -/
  burnsideAbsIrred : G0Galois.BurnsideAbsIrred
  /-- g0-mod-galois, LEAF: R14 with its published determinant clause (Shimura 1971 Thm 7.14,
  Deligne 1971; UNVERIFIED locators). Used instead of the bundle's `r14` alone, whose statement
  omits the determinant (g0-mod-galois' finding). -/
  r14Det : G0Galois.R14Det
  /-- g0-mod-galois G9, GLUE (N5's de Rham descent lemma, appendix). -/
  g9Glue : G0Galois.G9Glue
  /-- g0-mod-galois G10, GLUE (oddness; g0-assemble replaced its two removed placeholder
  hypotheses T11, T12 by the bundle's concrete T11a, T11b). -/
  g10Glue : G0Galois.G10Glue
  /-- g0-mod-galois G12, GLUE (Hodge–Tate weight comparison). -/
  g12Weight : G0Galois.G12Weight
  /-- g0-mod-galois, GLUE (from T9): `det V_ℓ(A) = χ_ℓ^{dim A}`. -/
  detTate : G0Galois.DetTate
  /-- g0-mod-newform, GLUE (from Kronecker–Weber): finite-image characters are Dirichlet
  characters at Frobenius. -/
  dirichletOfFinite : G0ModNewform.DirichletOfFinite
  /-- R17 as a concrete statement (kernel `LadicCond.CarayolR17'`), LEAF (Carayol 1986,
  Théorème (A); faithful per the locator audit). The bundle's `r17` is still an `opaque`
  placeholder, unused on this route. -/
  carayolR17 : LadicCond.CarayolR17'
  /-- kernel glue (Serre–Tate §2, Herbrand): the Swan conductor does not depend on the level. -/
  swanIndependent : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)
  /-- kernel glue L8: `Sw = ∫ codim V^{G^u}`. -/
  swanIntegral : LadicCond.SwanIntegral
  /-- kernel glue: an adapted level exists (`ρ(P_p)` finite for `ℓ ≠ p`). -/
  adaptedExists : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)
  /-- linked-tate, GLUE (given the leaf R7a): good reduction at every DVR with `3` a unit makes
  inertia above `p ∉ {3, ℓ}` fix the `ℓ`-power torsion points of base changes (the point-level
  transport half of G3). -/
  goodRedTorsion : LinkedTate.GoodRedTorsion
  /-- linked-tate, GLUE (literature-backed: Mumford §19 Thm 3, Albert's classification): the QM
  model with `EndDivision` has `rank_ℤ End = 4`. -/
  qmEndRank : LinkedTate.QMEndRank
  /-- neron-lg's glue N1-g1 (copied by frob-pieces): an abelian variety over a number field `L`
  spreads out to an abelian scheme over `𝓞_L[1/f]` for some `f ≠ 0` (EGA IV₃ §8). Replaces, with
  `properSmoothGenConnected` and the textbook leaves T3 (I2-NMP), T4 (I2-Red), linked-tate's
  `linkedFrob` (linked-frob: `LinkedFrobRed.linkedFrob_of_textbook`). -/
  abVarSpreadsOut : FrobPiecesNeron.AbVarSpreadsOut
  /-- frob-pieces, LEAF candidate (Zariski's connectedness theorem, EGA III₁ 4.3): a proper smooth
  morphism with geometrically connected generic fibre has geometrically connected fibres. -/
  properSmoothGenConnected : FrobPiecesNeron.ProperSmoothGenConnected
  /-- linked-tate, GLUE (N5 L819-852, D1-D4): Glazer's wild ramification (`RhoRamWild`) for the
  canonical descended operators, with `γ₀ = β/a` under an embedding `ℚ̄ → ℂ`. -/
  linkedRam : UnramTate.LinkedRam

/-- **`GluePieces3` from `GluePieces4`** (linked-frob): `linkedFrob` by
`LinkedFrobRed.linkedFrob_of_textbook`. -/
theorem gluePieces3_of_gluePieces4 (t : TextbookLeaves) (gp4 : GluePieces4) : GluePieces3 where
  mulIsogeny := gp4.mulIsogeny
  rigidityHom := gp4.rigidityHom
  finiteDescends := gp4.finiteDescends
  fibreComTrivial := gp4.fibreComTrivial
  analyticUniformizationUnique := gp4.analyticUniformizationUnique
  metrizationDimUnique := gp4.metrizationDimUnique
  metrizationExists := gp4.metrizationExists
  productMetrizationGeo := gp4.productMetrizationGeo
  hodgeLineBaseChange := gp4.hodgeLineBaseChange
  fibreQMPeriod := gp4.fibreQMPeriod
  thetaRatiosAlgebraic := gp4.thetaRatiosAlgebraic
  fibreCoverExists := gp4.fibreCoverExists
  kernelFieldExists := gp4.kernelFieldExists
  unramifiedSup := gp4.unramifiedSup
  burnsideAbsIrred := gp4.burnsideAbsIrred
  r14Det := gp4.r14Det
  g9Glue := gp4.g9Glue
  g10Glue := gp4.g10Glue
  g12Weight := gp4.g12Weight
  detTate := gp4.detTate
  dirichletOfFinite := gp4.dirichletOfFinite
  carayolR17 := gp4.carayolR17
  swanIndependent := gp4.swanIndependent
  swanIntegral := gp4.swanIntegral
  adaptedExists := gp4.adaptedExists
  goodRedTorsion := gp4.goodRedTorsion
  qmEndRank := gp4.qmEndRank
  linkedRam := gp4.linkedRam
  linkedFrob := LinkedFrobRed.linkedFrob_of_textbook t gp4.abVarSpreadsOut gp4.properSmoothGenConnected

/-- **G0 after linked-frob**: the leaf bundles and `GluePieces4` imply `ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves4 (r : ResearchLeaves) (t : TextbookLeaves) (gp4 : GluePieces4) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leaves3 r t (gluePieces3_of_gluePieces4 t gp4)

end HSyn

end

end LinkedFrobBundleSec

#print axioms LinkedFrobRed.tmOf_eq
#print axioms LinkedFrobRed.linkedFrob_of_algFrobLink
#print axioms LinkedFrobRed.linkedFrob_of_algFrobRed
#print axioms LinkedFrobRed.linkedFrob_of_gen
#print axioms LinkedFrobRed.linkedFrob_of_goodRed_nmp
#print axioms LinkedFrobRed.linkedFrob_of_neron_nmp
#print axioms LinkedFrobRed.linkedFrob_of_textbook
#print axioms HSyn.gluePieces3_of_gluePieces4
#print axioms HSyn.sixContactMin_of_leaves4
