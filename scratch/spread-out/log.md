# spread-out log (task spread-out, 2026-11-13)

Target: neron-lg glue N1-g1 `AbVarSpreadsOut` (scratch/neron-lg/NeronLG.lean:468, with
`HasAbelianSchemeAway` :451). Merged origin/wip/frob-pieces (60340bed) at start.

## Survey: Mathlib 4.35 (pinned 56a00585) and vendored Tau Ceti on limits / spreading out

VERIFIED (read in source):
* `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` (Yang–Merten; follows EGA IV 8 / Stacks 01YT):
  setting `D : I ⥤ Scheme`, cofiltered, `IsAffineHom (D.map f)`, `c : Cone D`, `IsLimit c`.
  - `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` (Stacks 01ZC, surjective half of
    EGA IV₃ 8.8.2 (i)): `D i` qcqs, `X → S` LFP, every `S`-map `lim D → X` factors through some `D i`.
  - `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`,
    `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType` (injective half; `D i` qc, `X → S` LFT).
  - `Scheme.preservesColimit_yoneda` (Hom_S(-, X) turns such limits into filtered colimits).
  - `Scheme.nonempty_of_isLimit`, `compactSpace_of_isLimit`, `exists_isAffine_of_isLimit`,
    `exists_isOpenCover_and_isAffine(_of_finite)`, `OpenCover.exists_of_isCofiltered_of_finite`
    (descent of finite affine open covers), sections `exists_appTop_π_eq_of_isLimit`, Γ preserves the limit.
  - `opensDiagram`/`isLimitOpensCone` (restriction of the diagram to `Over i`, via
    `isLimitOfIsPullbackOfIsConnected` and `Functor.Initial.isLimitWhiskerEquiv (Over.forget i)`).
* NOT in Mathlib 4.35: descent of finitely presented *schemes* (EGA IV₃ 8.8.2 (ii), Stacks 01ZM),
  descent of properness (EGA IV₃ 8.10.5 (xii)), of smoothness (EGA IV₄ 17.7.8 (ii)), of group
  structures (no statement about `GrpObj` over limits). `Mathlib/AlgebraicGeometry/SpreadingOut.lean`
  is about spreading out morphisms from stalks (germs), not limits.
* Category theory available: `Over.pullback f` is `Braided` (hence `Monoidal`) for the cartesian
  structure on `Over` (`Monoidal/Cartesian/Over.lean`); `Functor.grpObjObj`, `GrpObj.ofIso`,
  `NatTrans.IsMonoidal.of_cartesianMonoidalCategory` (every nat. trans. between monoidal functors of
  cartesian categories is monoidal); `Over.pullbackComp` (defined by conjugation, no component lemmas).
* Tau Ceti (~/tc-oct16, ~/tc-nov01, ~/tc-main, and the ~1600 vendored modules): no descent of
  schemes / properness / smoothness over limits (grep for EGA 8.8.2, 8.10.5, 17.7.8, Stacks 01ZM,
  081C, 07RP, "spread": no hits in AlgebraicGeometry). Nothing to vendor.
* Prior project work: wip/morph-descend (`MorphDescend.exists_descend`, morphisms over ℚ̄ = colim L)
  uses the same Mathlib lemmas; recipe for ring colimit → `IsLimit` of Spec cone reused.

## Plan
Leaves (EGA IV, published, locators UNVERIFIED): 8.8.2 (ii) objects; 8.10.5 (xii) proper;
17.7.8 (ii) smooth.  Glue to prove: descent of the group structure (from Mathlib's 8.8.2 (i)
halves), the colimit `L = colim 𝓞_L[1/n!]`, and the transfer to every presentation of 𝓞_L[1/f].

## Results (all VERIFIED by compilation unless marked)

New Contrib files (Mathlib + ZInQKernel.HDecomp.Objects only; each `lake build` OK):
* `ZInQKernel/Contrib/SpreadOut/GrpDescent.lean` — abstract: `GrpAx`, `FAx`, `grpAx_map_iff`
  (axioms for the image data ⟺ F identifies both sides of each axiom), `CompatM/U/I`,
  `fAx_of_compat`, `compat*_transport` (along θ : P ⋙ F' ≅ F; monoidality of θ is automatic in the
  cartesian setting), `compat*_of_lift`, `compat*_of_isMonHom`, `isMonHom_of_compat`,
  `isMonHom_descend`.
* `ZInQKernel/Contrib/SpreadOut/Limit.lean` — `pbNat` (explicit `Over.pullbackComp`, components
  are explicit pullback lifts), `bcDiag`/`bcCone`/`bcConeIsLimit` (l ↦ Y ×_{D k} D l over `Over k`,
  limit Y ×_{D k} lim, via `isLimitOfIsPullbackOfIsConnected` + `Functor.Initial`), `exists_lift`
  (EGA IV 8.8.2 (i) surjectivity in `Over` form), `exists_map_eq` (injectivity).
* `ZInQKernel/Contrib/SpreadOut/Spread.lean` — the leaves `EGAIV_8_8_2_ii`, `EGAIV_8_10_5_xii`,
  `EGAIV_17_7_8_ii` (index: nonempty directed preorder `J`, diagram `Jᵒᵖ ⥤ Scheme`, qcqs terms,
  affine transition maps); finiteness instances for ⊗ and base change in `Over S`; `Ev` (eventually)
  calculus; `Stage`; `exists_grp_stage`; `exists_grpObj_descend` (smooth proper group scheme over
  lim D descends to a stage, with an isomorphism of group schemes).
* `ZInQKernel/Contrib/SpreadOut/NumberField.lean` — `ringCoconeIsColimit` (L = colim_n 𝓞_L[1/n!]),
  `specConeIsLimit`, `abVarSpreadsOut_of_ega` (body of N1-g1, any presentation R of 𝓞_L[1/n!]).

Scratch: `scratch/spread-out/SpreadOut.lean` (build.sh = imports + part_n1.lean + axiom prints):
`ZInQ.SpreadOutN1.abVarSpreadsOut_of_ega : EGAIV_8_8_2_ii → EGAIV_8_10_5_xii → EGAIV_17_7_8_ii →
AbVarSpreadsOut`, with `HasAbelianSchemeAway`, `AbVarSpreadsOut` verbatim from
scratch/neron-lg/NeronLG.lean (py/verbatim_check.py: ALL VERBATIM).  `lake env lean` exit 0, ~5 s
(after the Contrib modules are built), 7 axiom prints all [propext, Classical.choice, Quot.sound]
(run2.txt).

Compile pitfalls met (recorded for reuse):
* `simp` with `pullback.lift_fst` fails on Scheme pullbacks unless
  `set_option backward.isDefEq.respectTransparency false` (as in Mathlib's AffineTransitionLimit).
* goals with `pullback.fst (Over.mk (pullback.snd ..)).hom ..` (from unfolding `Over.pullback`):
  `erw` times out; fix by `ext1; show <explicit pullback.lift form>` and work with syntactic pullbacks.
* `open MonObj` makes `ι` a notation: `Cocone` field `ι :=` fails to parse.
* passing `B.X : Over (Spec L)` where `Over c.pt` is expected (c.pt defeq Spec L) timed out in the
  final `exact`; fix: restate the descent result with explicit `Spec.map (ofHom toL)` in a `have`.
* `open DefFaltings` in neron-lg's opens resolves to `ZInQ.DefFaltings`: the verbatim copies must
  live in a namespace under `ZInQ`.

Combined check `scratch/spread-out/SpreadOutFull.lean` (build_full.sh = frob-pieces'
FrobPiecesFull.lean unchanged + import ZInQKernel.Contrib.SpreadOut.NumberField + part_full.lean):
`lake env lean` exit 0, 2 min 23 s, 117 axiom prints, all [propext, Classical.choice, Quot.sound]
(one print wraps over two lines), 0 sorry (run_full1.txt).  New theorems:
`ZInQ.SpreadOutFull.frobPiecesNeron_abVarSpreadsOut` (frob-pieces' copy of N1-g1 from the leaves),
`ZInQ.SpreadOutFull.algFrobRed_of_ega_nmp : EGAIV_8_8_2_ii → EGAIV_8_10_5_xii → EGAIV_17_7_8_ii →
ProperSmoothGenConnected → I2-Red → I2-NMP → FrobTrace.AlgFrobRed`, `tateBridge35_of_ega_nmp`.
Before the first run: `lake build` of the 19 non-Mathlib imports (12 s, all cached).
