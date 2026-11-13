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
