/-! ## linked-tate: `GluePieces3`, g0-assemble's `GluePieces2` with its fields 27 (`modelG3G6`) and
28 (`linkedTateData`) replaced by seven smaller glue Props (the fields before them are copied
verbatim, with their docstrings, from `scratch/g0-assemble/parts/90_bundle.lean`). -/

section LinkedTateBundleSec

noncomputable section

namespace HSyn

open G0Split

structure GluePieces3 : Prop where
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
  /-- linked-tate, GLUE (N5 L777-786): `FrobTraceLink` for the canonical operators `tmOf`. -/
  linkedFrob : UnramTate.LinkedFrob
  /-- linked-tate, GLUE (N5 L819-852, D1, D3; field half): the upper breaks of the kernel field
  `L'` at `p ≤ D` are `≤ U₀`, and `L'` is tame at `p > D`. -/
  kernelFieldBreaks : UnramTate.KernelFieldBreaks
  /-- linked-tate, GLUE (definitions, Mathlib-level): local inertia lands in a global inertia group. -/
  localInertiaGlobal : UnramTate.LocalInertiaGlobal
  /-- linked-tate, GLUE (definitions, Mathlib-level): `G_{ℚ_p}^t ⊆` inertia for `t > 0`. -/
  upperAbsInertia : UnramTate.UpperAbsInertia
  /-- linked-tate, GLUE (N5 L819-852 at `p = 3`): `G_{ℚ_3}^t`, `t > U₀`, acts trivially on
  `V₅` of the QM model. -/
  tateRamAtThree : UnramTate.TateRamAtThree

/-- **`GluePieces2` from `GluePieces3`** (linked-tate): the two joint fields of g0-assemble are
proved, `modelG3G6` from `FibreSimple` (itself from g0-fibresimple's fields, as in
`gluePieces_of_gluePieces2`), `GoodRedTorsion` and the bundle's R6, R7a, T5, and
`linkedTateData` from T7, T26, `FibreSimple`, `QMEndRank`, `LinkedFrob`, and `LinkedRam`
(itself from G3 and `KernelFieldBreaks`, `LocalInertiaGlobal`, `UpperAbsInertia`, `TateRamAtThree`). -/
theorem gluePieces2_of_gluePieces3 (r : ResearchLeaves) (t : TextbookLeaves) (gp3 : GluePieces3) :
    GluePieces2 where
  mulIsogeny := gp3.mulIsogeny
  rigidityHom := gp3.rigidityHom
  finiteDescends := gp3.finiteDescends
  fibreComTrivial := gp3.fibreComTrivial
  analyticUniformizationUnique := gp3.analyticUniformizationUnique
  metrizationDimUnique := gp3.metrizationDimUnique
  metrizationExists := gp3.metrizationExists
  productMetrizationGeo := gp3.productMetrizationGeo
  hodgeLineBaseChange := gp3.hodgeLineBaseChange
  fibreQMPeriod := gp3.fibreQMPeriod
  thetaRatiosAlgebraic := gp3.thetaRatiosAlgebraic
  fibreCoverExists := gp3.fibreCoverExists
  kernelFieldExists := gp3.kernelFieldExists
  unramifiedSup := gp3.unramifiedSup
  burnsideAbsIrred := gp3.burnsideAbsIrred
  r14Det := gp3.r14Det
  g9Glue := gp3.g9Glue
  g10Glue := gp3.g10Glue
  g12Weight := gp3.g12Weight
  detTate := gp3.detTate
  dirichletOfFinite := gp3.dirichletOfFinite
  carayolR17 := gp3.carayolR17
  swanIndependent := gp3.swanIndependent
  swanIntegral := gp3.swanIntegral
  adaptedExists := gp3.adaptedExists
  modelG3G6 := LinkedTate.modelG3G6_of
    (G0FibreSimple.fibreSimple_of_leaves t gp3.mulIsogeny gp3.rigidityHom
      ⟨gp3.finiteDescends, gp3.fibreComTrivial⟩)
    (LinkedTate.qmModelG3_of r.r7a r.r6 t.t5
      (LinkedTate.goodRedG3Bridge_of_torsion gp3.goodRedTorsion))
  linkedTateData := LinkedTate.linkedTateData_of_frobRam t.t7 t.t26
    (G0FibreSimple.fibreSimple_of_leaves t gp3.mulIsogeny gp3.rigidityHom
      ⟨gp3.finiteDescends, gp3.fibreComTrivial⟩)
    gp3.qmEndRank (UnramTate.linkedFrobRam_of gp3.linkedFrob
      (UnramTate.linkedRam_of
        (LinkedTate.qmModelG3_of r.r7a r.r6 t.t5
          (LinkedTate.goodRedG3Bridge_of_torsion gp3.goodRedTorsion))
        gp3.kernelFieldBreaks gp3.localInertiaGlobal gp3.upperAbsInertia gp3.tateRamAtThree))

/-- **G0 after linked-tate**: the leaf bundles and `GluePieces3` imply `ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves3 (r : ResearchLeaves) (t : TextbookLeaves) (gp3 : GluePieces3) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leaves2 r t (gluePieces2_of_gluePieces3 r t gp3)

end HSyn

end

end LinkedTateBundleSec

#print axioms HSyn.gluePieces2_of_gluePieces3
#print axioms HSyn.sixContactMin_of_leaves3
