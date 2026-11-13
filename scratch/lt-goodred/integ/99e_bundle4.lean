/-! ## lt-goodred: `GluePieces4`, linked-tate's `GluePieces3` without `goodRedTorsion` and `qmEndRank`

Both fields are now theorems: `LTGoodRed.goodRedTorsion : LinkedTate.GoodRedTorsion` (no hypothesis;
NOS is the antecedent of the Prop) and `LTGoodRed.QM.qmEndRank_of_leaves t.t6 t.t27 :
LinkedTate.QMEndRank` (I3.M1 = `TextbookLeaves.t6`, T27 = `TextbookLeaves.t27`). The other 27 fields
are copied verbatim, with their docstrings, from `scratch/linked-tate/parts/99_bundle3.lean`. -/

section LTGoodRedBundleSec

noncomputable section

namespace HSyn

open G0Split

/-- linked-tate's `GluePieces3` with its fields `goodRedTorsion` and `qmEndRank` removed (both
proved by lt-goodred). -/
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
  /-- linked-tate, GLUE (N5 L777-786): `FrobTraceLink` for the canonical operators `tmOf`. -/
  linkedFrob : UnramTate.LinkedFrob
  /-- linked-tate, GLUE (N5 L819-852, D1-D4): Glazer's wild ramification (`RhoRamWild`) for the
  canonical descended operators, with `γ₀ = β/a` under an embedding `ℚ̄ → ℂ`. -/
  linkedRam : UnramTate.LinkedRam

/-- **`GluePieces3` from `GluePieces4` and the textbook leaves** (lt-goodred). -/
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
  linkedFrob := gp4.linkedFrob
  linkedRam := gp4.linkedRam
  goodRedTorsion := LTGoodRed.goodRedTorsion
  qmEndRank := LTGoodRed.QM.qmEndRank_of_leaves t.t6 t.t27

/-- **G0 after lt-goodred**: the leaf bundles and `GluePieces4` imply `ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves4 (r : ResearchLeaves) (t : TextbookLeaves) (gp4 : GluePieces4) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leaves3 r t (gluePieces3_of_gluePieces4 t gp4)

end HSyn

end

end LTGoodRedBundleSec

#print axioms HSyn.gluePieces3_of_gluePieces4
#print axioms HSyn.sixContactMin_of_leaves4
