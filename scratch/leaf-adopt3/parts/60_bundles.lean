/-- **The research-level leaves of route P** (note §2.1), bundled. Placeholders are
uninterpreted. Genuine statements: `R4` (pkg-I1), `R6`, `R7` (pkg-I2), `R9` (pkg-I3), `R10`,
`R11`+`R12`, `R13` (pkg-I4), `R14`, `R15` (§1 here); leaf-adopt (2026-11-12): R1 (a, c, d),
R2, R5 (leaf-qm-fp, repaired), R16 (leaf-modcurves), R19-R21 and H5 (def-faltings);
leaf-adopt2 (2026-11-12): R3, R18, R22 (leaf-push2). Remaining placeholders: R1(b), R17. -/
structure ResearchLeaves : Prop where
  /-- R1 (a), (c), (d), `π₀(X₆) = 1` (rv-blueprints Q4), R1 at level one, R2 with biconditional CM
  clauses (Q5) and R5 on points of `X₆`, on one `Y₃`, `X₆` (leaf-qm-fp, repaired by leaf-adopt).
  Premise Lemma P of rv-qm-polar (type-`μ` polarization exists and is unique), see the definition. -/
  r1r2 : LeafAdopt.R1R2fpRep
  /-- R1(b), complex uniformization in family form (Q3): still a placeholder. -/
  r1an : R01b_ComplexUniformization
  /-- R1(d), Shimura reciprocity, object form (leaf-qm-fp; premise Lemma P, rv-qm-polar). -/
  r1rec : LeafQM.AV.R1rec
  /-- R3, Lin–Yang over `ℂ`, existential and polarization-free (leaf-push2; premise Lemma P). -/
  r3 : ZInQ.LeafPush2.R03_LinYang
  r4 : PkgI1.ThetaModularity
  /-- R5(ii), González–Rotger Thm 5.12, fields of moduli (= rv-blueprints' R5fpStrong, Q2;
  premise Lemma P, rv-qm-polar). -/
  r5 : LeafQM.AV.R5fp
  /-- R5(i), González–Rotger Prop. 5.6, `#CM(R) = 2^b h(R)` (premise Lemma P, rv-qm-polar). -/
  r5count : LeafQM.AV.R5fpCount
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r7b : PkgI2.SerreTatePotentialGood.{0}
  r8 : PkgI2.GrothendieckMonodromy.{0}
  r9a : PkgI3.FaltingsSemisimple
  r9b : PkgI3.FaltingsTate
  r10 : PkgI4.DeRhamComparison
  /-- R11 (Berger) and R12 (Pan) enter through their joint consequence: Pan's theorem with "de Rham
  at `p`" in place of "potentially semistable at `p`" (pkg-I4). `B_st` is not needed by the glue.
  Both theorems remain separate leaves in the count. -/
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  r14 : EigenformRepExists
  r15 : DeligneSerreConseq
  /-- R16, Eichler–Shimura in `J₁(N)`, existential form for every `K_N` model (leaf-modcurves). -/
  r16 : LeafModCurves.R16_EichlerShimuraJ1'
  r17 : R17_Carayol
  /-- R18, Javanpeykar, over leaf-push2's stable Faltings height on `PkgI3.AbVar` (with H5). -/
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  /-- R19-R21 over def-faltings' `stableFaltingsHeight` (not yet known non-vacuous: AN3 open). -/
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r20 : ZInQ.DefFaltings.R20_FaltingsLemma5
  r21 : ZInQ.DefFaltings.R21_Bost
  /-- R22, Pazuki's upper half, over all uniformizations and period matrices (leaf-push2). -/
  r22 : ZInQ.LeafPush2.R22_Pazuki
  /-- H5 (rv-blueprints F2): the stable height is finite and attained by Néron models. -/
  h5 : LeafAdopt.H5

/-- **The textbook foundations** (note §2.2), bundled. -/
structure TextbookLeaves : Prop where
  t1 : PkgI2.PurityBranchLocus.{0}
  t2 : PkgI2.AbhyankarDVR.{0}
  t3 : PkgI2.NeronMappingAbelianScheme.{0}
  t4 : PkgI2.ReductionTorsionBijective.{0}
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t9 : LeafPush.T09_WeilPairing.{0}
  t10 : T10_TateDuality
  /-- T11(a), Riemann/GAGA for endomorphisms (leaf-push2). -/
  t11a : ZInQ.LeafPush2.T11a_RiemannEnd
  /-- T11(b), rigidity of homomorphisms under extension of an algebraically closed field
  (leaf-push2). -/
  t11b : ZInQ.LeafPush2.T11b_Rigidity
  -- leaf-adopt2: T12 is glue (`ZInQ.LeafPush2.T12_ComplexConjEigen`, a target), no longer a field.
  t13 : SkolemNoether
  -- hsyn-fix: the cochain forms I6.2a′-c′ (rv-leaves-b repair 3; Mathlib does not yet compare
  -- `continuousCohomology` with inhomogeneous cochains). `PkgI6.BrauerHasse2` etc. remain in the file.
  t14a : PkgI6.BrauerHasse2C
  t14b : PkgI6.BrauerReciprocity2C
  t15 : PkgI6.LocalH2CardC
  t16a : ∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p
  t16b : PkgI6.LocalReciprocityUpper
  t17 : KroneckerWeber
  t18 : FrobeniusDense
  t19 : BrauerNesbitt
  t20 : GlueConductor.HilbertDifferentFormula
  t21 : GlueConductor.SerreDifferentBound
  t22a : PkgI6.HerbrandQuotient
  t22b : PkgI6.HerbrandTransitivity
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : EigenformTwist
  t25 : PkgI4.NewformOfEigenform
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomyYu
  t28 : PkgI1.IgusaClebschSeparation
  t29a : ∀ (p : ℕ) [Fact p.Prime], LeafPush.T29a_DivisionNormalizer p
  t29b : ∀ (p : ℕ) [Fact p.Prime], LeafPush.T29b_SplitNormalizer p
  t30 : GlueDescent.B2Q.LeafSqrtCrit
  t31 : GlueDescent.B2Q.LeafUnramified
  -- leaf-adopt: T32 is glue (`HSyn.t32a_glue`, `HSyn.t32b_glue`), no longer a field.
  /-- T33 (new, leaf-modcurves): existence of the Jacobian of a pointed curve (Weil; Milne 1986). -/
  t33 : LeafModCurves.JacobianExists ℚ
  /-- T34 (new, leaf-modcurves): `dim J₁(N)` is the genus of `Γ₁(N)` (Shimura 1971 Prop. 1.40 with
  §6.7 and `dim Jac = genus`). -/
  t34 : LeafModCurves.DimJ1Genus
  /-- T35 (new, leaf-push2): analytic uniformization of `A(ℂ)_σ` by `ℂ^{dim A}` with a full
  lattice (Mumford §1 with GAGA; AN3 for abelian varieties). -/
  t35 : ZInQ.LeafPush2.UniformizationExists

