# modular-split results log

Build: `.lake/build/lib/lean/ZInQKernel` copied from ~/dzq-wt/leaf-fold8 (sources identical except
`Contrib/CloudW07JacobiansCurves/`, verified by `git diff --name-only`); `lake build
ZInQKernel.OneProof.H.TailT ZInQKernel.OneProof.H.LPrefix` exits 0 (VERIFIED, 11-14 11:3x).

## r15 `HDec.HSyn.DeligneSerreConseq` — DONE
- `scratch/modular-split/R15.lean`: `ModularSplit.deligneSerreConseq_of_ds : DSThm966 → HDec.HSyn.DeligneSerreConseq`.
  Leaf: `ZInQ.Contrib.HodgeSplit.DSThm966` (Deligne–Serre 1974 Thm 4.1 / Diamond–Shurman Thm 9.6.6; already a
  published-form LEAF of the bundle, field `dsThm966`). Glue proved: `artinTransport_finite` (copy of hodge-split's
  `artinTransport_proof`, returning finite image), `attachedConj_proof` (T18+T19, kernel).
  Compile: `lake env lean scratch/modular-split/R15.lean` → axioms [propext, Classical.choice, Quot.sound]. VERIFIED.

## r17 `LadicCond.CarayolR17'` — REDUCED (not done: remaining leaf is a consequence, not printed form)
- `scratch/modular-split/R17.lean`: `ModularSplit.R17.carayolR17'_of_realization : CarayolRealization → LadicCond.CarayolR17'`.
  New glue proved: `condExp_conj` (Serre–Tate conductor exponent invariant under conjugation; via `invariants_conj`,
  `codimInv_conj`, `isAdapted_conj`, `swan_conj`), plus `attachedConj_proof` (T18+T19).
  Remaining leaf `CarayolRealization` (∃ semisimple attached ρ with condExp = v_p(N) at all p ≠ ℓ): consequence of
  Carayol 1986 Thm (A) + Casselman 1973 + Ribet irreducibility; not printed form (automorphic reps / LLC not in Mathlib).
  Compile: axioms [propext, Classical.choice, Quot.sound]. VERIFIED.

## eigenformHTNew `ZInQ.Contrib.HodgeSplit.EigenformHTNew` — REDUCED (not done)
- `scratch/modular-split/EigenHT.lean`: `ModularSplit.EigenHT.eigenformHTNew_of_realization : KatoRealization → EigenformHTNew`
  from `attachedConj_proof` + `htConj_proof` (kernel). Remaining leaf `KatoRealization` (∃ semisimple attached ρ with
  HT weights {0,1−k}): Kato 2004 §9 at V_f^∨ + Ribet irreducibility; consequence (dualized), V_f not definable.
  Compile: axioms [propext, Classical.choice, Quot.sound]. VERIFIED.

## dimJacobianEqGenus `ZInQ.Contrib.CurvesG.DimJacobianEqGenus` — REDUCED to one project GLUE, no literature leaf
- Built `ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists`, `...Curve.CanonicalDegree`, `Contrib.CurvesG.GenusSplit`,
  `Contrib.Dim.SmoothStalk`, `Contrib.Dim.Basic` (lake build exit 0).
- `scratch/modular-split/DimJac.lean`:
  `ModularSplit.DimJac.dim_jacobian_eq_arithmeticGenus` (J.dim = arithmeticGenus ℚ X = dim H¹(X,𝒪), proved from the vendored
  library: exists_abelianVariety_picardDegreeZero (smooth of rel. dim = arithmeticGenus), isAlbanese_abelJacobiMap,
  IsJacobian.unique, Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension);
  `ModularSplit.DimJac.dimJacobianEqGenus_of_glue : H0DifferentialsEqHolo → DimJacobianEqGenus` (+ library Serre duality
  finrankH_relativeDifferentials_zero_eq_genus).
  Remaining GLUE `H0DifferentialsEqHolo`: dim_ℚ H⁰(X, Ω¹_{X/ℚ}) = CurvesG.fieldGenus F (textbook sheaf theory; no published-theorem content).
  Milne Prop. 2.1 and Serre duality are no longer leaves. Compile: axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- (12:3x) `EigenHT.lean` extended: `dualGR` (contragredient GaloisRep, continuity proved), `dualGR_isIrreducible` (proved),
  named GLUE `HTDual` (HT weights of the contragredient are negated, Hodge–Tate case card S = n), leaf candidate
  `KatoRealizationCoh` (∃ irreducible ρ, geometric-Frobenius trace a_p, HT weights {0,k−1}),
  `katoRealization_of_coh : KatoRealizationCoh → HTDual → KatoRealization`,
  `eigenformHTNew_of_coh : KatoRealizationCoh → HTDual → EigenformHTNew`. Compile: standard axioms. VERIFIED.
