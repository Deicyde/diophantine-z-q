# rv-gluepieces2 results log

Target: the 27 fields of `HSyn.GluePieces2` in scratch/g0-assemble/G0Assemble.lean (L41938-41998).

- VERIFIED (cmp/diff): scratch/g0-assemble/Leaves.lean differs from scratch/h-decomposition/Leaves.lean
  (current, post pin-apply) exactly by pin-apply's patch: `R1famProps`, `R1univProps`, `QMFamily`,
  `IsFibreOf` and namespace `Pin` are absent from G0Assemble.lean; its `R1fpProps` is the
  pre-repair 4-clause version (no fam/univ clauses).

## QM-PIN fields (4 fibreComTrivial, 10 fibreQMPeriod, 13 kernelFieldExists, 27 modelG3G6)

- VERIFIED (read): all four quantify over every `(Y, Φ, π)` with `R1fpProps Y Φ ∧ R2fpProps Y Φ π`
  (directly, or through `FibreCtx`, L39149). In G0Assemble.lean `R1fpProps` (L15152) is the
  pre-repair 4-clause list (proper, smooth rel. dim 1, a ℚ̄-point, naturality).
- VERIFIED (read, already proved in the file): parts/40_fibresimple.lean §5
  `r1fpProps_twistBy`, `r2fpProps_twistBy`, `fibreComTrivial_twisted`: under the 4-clause list,
  `FibreComTrivial` applied to `Φ ∘ σ` asserts NoCM at every rational value whose π-fibre a
  natural point-relabeling σ can exchange with the fibre over J(u). So the field is equivalent to
  an open arithmetic statement (no ℚ-isomorphism of finite étale fibres between a non-contact
  rational fibre and a rational CM fibre). Same mechanism for 10, 13 (via NoCM in End⁰ = B) and
  27 (G6 half).
- 27 `ModelG3G6`, G3 half: not pin-dependent. `IsQMModel` makes `A = (PK.A)_L` with `PK : QML3 K`;
  `Level3` (L14331ff) = `𝒪`-linear `η : 𝒪 → A(K)` with kernel `3𝒪`, i.e. full rational 3-torsion
  on a surface. Raynaud (semistable at p ≠ 3) + potentially good reduction of QM surfaces ⇒ good
  reduction at p ≠ 3; `G3Out` (L37281) excludes p = ℓ. TRUE (STANDARD).
- 27, G6 half: noncommutativity from `PK.q.iota` (injective) after base change: TRUE. `EndDivision`
  of `A_{L'}` needs NoCM of `P` (CM ⇒ `A_ℚ̄ ≅ E²`): pin-dependent.

## Pinned rebase check (Lean)

- `build_prefix.sh`: scratch/h-decomposition/Leaves.lean (post pin-apply, verbatim) → olean/LPrefix.olean:
  exit 0 in 603 s, 0 errors, 190 `#print axioms` lines (VERIFIED, olean/prefix_out.txt).
- Tail = `import LPrefix` + g0-assemble's imports_extra + g0-assemble's parts verbatim except
  parts/40_fibresimple.lean (§5 demo lemmas `r1fpProps_twistBy`, `fibreComTrivial_twisted` take
  `R1famProps ∧ R1univProps` for the twisted Φ as an extra hypothesis; they are not used
  downstream) + checks/c1_g10.lean (g10-odd L102-239 verbatim + `g10Glue_of_conjTwist_new`).
- `ctail.sh Tail.lean` (8185 lines; started 06:43:48, finished 06:46:17, ~150 s): **0 errors, no
  `sorry`**, 7 `#print axioms` reports, all `[propext, Classical.choice, Quot.sound]`, including
  `HSyn.gluePieces_of_gluePieces2`, `HSyn.sixContactMin_of_leaves2` and
  `G0Galois.g10Glue_of_conjTwist_new` (VERIFIED, olean/Tail_out.txt).
  ⇒ g0-assemble's composite compiles unchanged over the pinned `R1fpProps` (6 clauses); only the
  two §5 demonstration lemmas of 40_fibresimple needed the extra hypothesis. The 27 field
  statements are textually unchanged, and over the pinned Leaves their `R1fpProps` hypotheses
  are stronger, so every field is (weakly) easier.
  ⇒ g10-odd's `ConjTwistNontrivial → G10Glue` holds for g0-assemble's changed `G10Glue`.

## Proved fields, re-checked on G0Assemble's own constants (over the pinned prefix)

- Layout changed: olean/TailBase.olean (parts, 8029 lines): exit 0 in 152 s, 0 errors. Each
  check file `checks/X.lean` compiles as `olean/Check_X.lean` = `import TailBase` + body.
- c1_g10: exit 0 in 47 s; `G0Galois.g10Glue_of_conjTwist_new : ConjTwistNontrivial → G10Glue`
  standard axioms (VERIFIED).
- c2_proved: first run failed (`eq_of_finrank_one` lives in metrization's ExtLine.lean); with the
  ExtLine body added: exit 0 in 40 s, 0 errors. Standard axioms (VERIFIED) for
  `RvGP2.finiteDescends : G0FibreSimple.FiniteDescends` (field 3),
  `RvGP2.unramifiedSup : G0ModField.UnramifiedSup` (field 14),
  `RvGP2.metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique` (field 6).
- c3_swan: swan's All.lean minus imports, first run: 47 errors, all "has already been declared"
  (Leaves.lean already contains t-different's `TDifferent` and `PkgI6.herbrandQuotient`); with that
  block omitted: exit 0 in 29 s, 0 errors. Standard axioms (VERIFIED) for
  `RvGP2.swanIndependent` (field 24), `RvGP2.swanIntegral` (field 25), `RvGP2.adaptedExists`
  (field 26), stated with G0Assemble's `LadicCond` constants.
- c4_dirichlet: body of x1-dirichlet's Dirichlet.lean; first run: "Ambiguous term" Qbar/GQ
  (Leaves.lean's `TSkolemKW.KW` declares its own `Qbar`, `GQ`); with `open TSkolemKW.KW hiding Qbar GQ`
  (the only change): exit 0 in 16 s. `RvGP2.dirichletOfFinite (t : HSyn.TextbookLeaves) :
  G0ModNewform.DirichletOfFinite := X1Dirichlet.dirichletOfFinite_of_kroneckerWeberCyclic t.t17`,
  standard axioms (VERIFIED). Field 22 follows from the bundle leaf t17.
- c5_g12det: g12-det's Integrate.lean minus its ModGalois copy and part_integrate (same recipe as
  build_int.py): exit 0 in 42 s, 0 errors. Standard axioms (VERIFIED):
  `RvGP2.detTate (t) hW hQ hD : G0Galois.DetTate` (weil-pairing's `T09_SymmIsogenyExists`,
  `IsogenyQuasiInverse`, `DivisiblePoints`, bundle `t.t26`), `RvGP2.g12Weight hSen hFI :
  G0Galois.G12Weight` (`SenTwist`, `FiniteImageHT`). Fields 19, 20 reduce to leaves outside the bundles.
- c6_metrization: ExtLine body + metrization's parts (build.sh order, without part_g0dim); 7
  off-route theorems `heightAdditivity_of_metrization*` removed (they use g0-heightadd's
  `heightAdditivity_of_geo`, which G0Assemble does not contain; G0Assemble took HeightAdd.lean from
  L390). Exit 0 in 10 s, 0 errors. Standard axioms (VERIFIED): `RvGP2.metrizationExists hH hU hN :
  ZInQ.G0HeightAdd.MetrizationExists` (`HodgeLatticeTheorem`, leaf `AnalyticUniformizationOfDim`,
  glue `JacDetNondegenerate`), `RvGP2.productMetrizationGeo hLS hPL : ProductMetrizationGeo`
  (glue `ProductLocalStructure`, `ProductHodgeLattice`).
- c7_heightbc: height-bc's Final.lean minus import/#print, with the single line `open PkgI3 (AbVar)`
  removed so that `AbVar` resolves to G0Assemble's `ZInQ.DefFaltings.AbVar` copy: exit 0 in 13 s,
  0 errors. `RvGP2.hodgeLineBaseChange h1 hc hω hl : G0StableBC.HodgeLineBaseChange` from
  `HodgeBCInjective`, `CotangentSpanBC`, `OmegaBaseChange`, `UniformizationLiftAnalytic`, standard
  axioms (VERIFIED). (Answers the height reviewer's transfer caveat.)
- Sweep of all *_out.txt: 0 errors, 0 `sorry`, no non-standard axiom line.
- c8_fibrecover: fibre-cover's FibreCover.lean L16-17 + L74-731 (its copies of the G0ModField
  statements dropped). First run: error at `rationalFibre_of_le`, `obtain ⟨-, -, -, hnat⟩ := h1`
  (fibre-cover predates pin-apply: R1fpProps now has 6 clauses); with `⟨-, -, -, hnat, -, -⟩`: exit 0
  in 12 s. `RvGP2.fibreCoverExists (t) hW hTS hU : G0ModField.FibreCoverExists` from bundle `t.t5`,
  `InnerTwistCount`, `PropTSAll`, `UnramifiedConjugates`, standard axioms (VERIFIED).

## Pin transfer for the six pin-dependent fields (Lean)

- gen_at.py generates checks/c9_pin_transfer.lean: `…At Y₀ Φ₀ π₀` forms of fields 4, 10, 12, 13,
  27, 28 produced mechanically from the fields' own text (binders `Y Φ π` dropped, `Y Φ π` →
  `Y₀ Φ₀ π₀`; a regex asserts no stray `Y`, `Φ`, `π` remain), plus transfer lemmas
  `RvGP2.Pin.fibreCtx_transfer`, `fibreCtx_mor`, `rationalFibre_transfer`.
- First run: exit 0 in 65 s, 0 errors, no sorry. Standard axioms (VERIFIED) for
  `G0FibreSimple.fibreComTrivial_of_at`, `HSyn.G0Split.ThetaPt.fibreQMPeriod_of_at`,
  `G0ModField.kernelFieldExists_of_at`, `G0ModField.fibreCoverExists_of_at`,
  `HSyn.G0AssembleMod.modelG3G6_of_at`, `HSyn.G0AssembleMod.linkedTateData_of_at`, each of shape
  `(hM : Pin.MobiusGlue) (hQM : R1R2fp) (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀)
   (h : FieldAt Y₀ Φ₀ π₀) : Field` — over the PINNED Leaves only (uses `R1fpProps.univ`).
- c10_g9: ZInQKernel/Contrib/G9/*.lean in import order without I3Layer, I4Layer, Statement (so the
  names resolve to G0Assemble's root `PkgI3`, `PkgI4`, `G0Galois`). First run: 101 errors
  (`modPMap`, `preTiltMap` unknown: inside `ZInQ.Contrib.G9.PkgI4.DR`, `open PkgI4…` resolved to
  the local namespace). With `open _root_.PkgI4[.DR]` added after the two `namespace PkgI4…` lines
  and the 12 later `open PkgI4…` lines widened to `_root_.PkgI4 ZInQ.Contrib.G9.PkgI4`: exit 0 in
  67 s, 0 errors. `RvGP2.g9Glue hBC hW : G0Galois.G9Glue` from `G9Bridge.AbVarBaseChange`,
  `G9Bridge.R10Weights`, standard axioms (VERIFIED).

## Field 15 proved (Lean)

- scratch/rv-gluepieces2/Burnside.lean (standalone, `import Mathlib`): `RvBurnside.adjoin_eq_top_of_algClosed`
  (Schur `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed` + Jacobson density
  `Module.Finite.toModuleEnd_moduleEnd_surjective`) and `RvBurnside.adjoin_eq_top_of_baseChange`
  (span of base-changed elements ⊇ the F'-algebra; finrank count `finrank_linearMap`,
  `finrank_baseChange`). `lake env lean`: 0 errors (linter warnings only).
- c11_burnside: Burnside.lean body + `RvGP2.burnsideAbsIrred : G0Galois.BurnsideAbsIrred`
  (with `F' = AlgebraicClosure F`; matrices through `LinearMap.toMatrixAlgEquiv b`): exit 0 in 13 s,
  0 errors, no sorry, standard axioms (VERIFIED). Field 15 is not a leaf: it is a Mathlib theorem.
