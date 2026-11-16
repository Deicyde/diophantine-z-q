# pic-repr results log

Base 0caafe66. Field `picRepresentableAbVar : T09Pic.PicRepresentableAbVar` (TailZ24.lean L289), bundle
`HDec.HSyn.OpenAddedLeaves17`.

## Statement
`T09Pic.PicRepresentableAbVar := ∀ (K : Type) [Field K] (A : PkgI3.AbVar K), ∃ P : Over (Spec (CommRingCat.of K)),
Nonempty ((picardFunctor A.X.hom).obj.RepresentableBy P)` — copied verbatim in `Statement.lean`, `rfl` against the
original: COMPILES (VERIFIED). No "locally of finite type" clause in the field.

## Library search (VERIFIED by reading)
- Vendored Jacobian-Challenge (`ZInQKernel/Contrib/CloudW07JacobiansCurves/`): full `picardFunctor` representable only
  for smooth proper geometrically integral **curves over separably closed fields**
  (`Picard/Representability.lean`, `exists_representableBy_picardFunctor`); chart = cohomology chart into the Hilbert
  scheme of finite flat subschemes (points) of a curve (`Hilbert/CurveRepresentability`). Over arbitrary fields only
  `Pic⁰` of curves descends (`Picard/FieldDescent.lean`, `exists_abelianVariety_picardDegreeZero`).
- Hilbert schemes in the tree: finite flat (points) of affine space and of curves only. No Quot/Hilbert of
  positive-dimensional subschemes, no quotients by finite flat group schemes / flat equivalence relations, no dual
  abelian variety construction (milne-compile's MilneQuasiInverse: annihilators, isogeny flatness, fpqc power descent).
- General vendored pieces that DO apply to abelian varieties over any field: `picardFunctorNormalizedGrp`,
  `isSheaf_zariski_picardFunctorNormalized`, `isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral`,
  `normalizedPicardIso` (Kleiman 9.2.5 form), `isRepresentable_of_representable_open_subfunctor` (group chart criterion).

## Compiled results (all `[propext, Classical.choice, Quot.sound]`)
- `Narrow.lean`: `PicRepr.smoothOfRelativeDimension_of_dim` (smooth irreducible K-scheme of Krull dim n is
  `SmoothOfRelativeDimension n`); `PicRepr.picRepresentable_dimOne_sepClosed` (field for `A.dim = 1`, `K` sep. closed).
- `Chart.lean`: `PicRepr.picChart_iff` (for X proper geom. integral with a rational point over any field K:
  chart hypothesis of the group criterion ⇔ representable; ⇐ by F = ⊤); `picRepresentableAbVar_of_chart`,
  `picChartAbVar_of_field`. So the chart Prop is equivalent to the field — NOT strictly smaller.
- `ZInQKernel/Contrib/OneProof/PicRepresentableAbVar.lean`: new leaf `PicRepr.PicRepresentableLFTAbVar` (printed
  Murre–Oort form: representable by P with `LocallyOfFiniteType P.hom`); `picRepresentableAbVar_of_lft` (the field);
  `PicRepr.PicLocFinType` (verbatim copy of pic-dict's `PicDict.PicLocFinType`, 4e95795b L2201) and
  `picLocFinType_of_lft`; `lft_of_picRepresentableAbVar_of_picLocFinType` (the leaf = conjunction of the two).

## Consumer audit (VERIFIED by reading; no field-read probe run)
picRepresentableAbVar → `T09Pic.t09SymmIsogenyExists_of_four` (TailZ24:807, only reader) → `T09_SymmIsogenyExists` →
(a) `tatePairingZl_of_leaves4` → `detTate_of_leaves4` → `G0Galois.DetTate` (`[NumberField K]`) → `g12Det_of`, applied
at `A.dim = 2` (`G12Det`, TailA:2078); (b) `t9_of_leaves5` → old T9 → `g8_g12` (`[NumberField K]`). Narrowing that
suffices: number fields, abelian surfaces. Dimension 1 (the case proved) does not reach the consumer.

## Build and fold checks
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.PicRepresentableAbVar`:
  Build completed successfully (13699 jobs); frozenTarget standard axioms (VERIFIED).
- `#discharges` (`Discharges.lean` → `discharges.txt`): `DISCHARGES [OpenAddedLeaves17.picRepresentableAbVar] by
  PicRepr.picRepresentableAbVar_of_lft, still assumes: [PicRepr.PicRepresentableLFTAbVar]`, standard axioms (VERIFIED).
- `autofold.py autofold.json --dry-run`: strict 34/11 on 45 -> 34/11 on 45; strictest 34/11 -> 34/11 (0 on main).
  `DryRunFold.lean` (dry-run output minus line 1) compiles; `sixContactMin_of_open36` standard axioms (VERIFIED).
- `PicRepr.PicLocFinType` textually identical to `PicDict.PicLocFinType` (pic-dict 4e95795b L2201; `AbVar` = `PkgI3.AbVar`
  under pic-dict's `open PkgI3`) (VERIFIED by diff; rfl not run, pic-dict not on main).
