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
