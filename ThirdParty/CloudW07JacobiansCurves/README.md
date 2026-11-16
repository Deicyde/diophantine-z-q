# cloud-w07: Jacobians and normal models of curves (frontier rows H-36, H-80)

Worker 7 of the owner's ten-worker fleet, issue
[elliotglazer/diophantine-z-q#83](https://github.com/elliotglazer/diophantine-z-q/issues/83).
Fixed statements: fork `main` `cba8157f7d5d09a4a3c8462aba2f3245494a870e` (unchanged at the base of
this branch, `f70ec251fd4bca6ae3115741c21fe661e7aaac3e`). No definition is changed; every new file
is in this directory.

| row | fixed statement | proof (this directory) |
|---|---|---|
| H-36 (`t33`) | `LeafModCurves.JacobianExists ℚ` (`ZInQKernel/HDecomp/ModCurves/Defs.lean`) | `ZInQ.Contrib.CloudW07JacobiansCurves.JacobianExists_proof` (`JacobianExists.lean`); general form `jacobianExists_of_field : ∀ K, LeafModCurves.JacobianExists K` |
| H-80 | `ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ` (`ZInQKernel/Contrib/CurvesG/CurveSplit.lean`) | `ZInQ.Contrib.CloudW07JacobiansCurves.NormalModelOfFunctionFieldQ_proof` (`NormalModel.lean`) |

`Checks.lean` restates both fixed types with `example` and prints the axioms; each theorem depends
only on `propext`, `Classical.choice` and `Quot.sound`.

## H-36: the Jacobian as an Albanese variety

The statement asks, for every smooth proper geometrically connected curve `X/K` with a `K`-point
`P₀`, for `J : PkgI3.AbVar K` and `aj : X ⟶ J.X` with `P₀ ≫ aj = η` and the Albanese universal
property among group-scheme homomorphisms (`LeafModCurves.IsJacobian`). AxiomMath/Mordell's
`Faltings.Jacobian` represents `Pic⁰` but has no Albanese property, and neither Mordell nor
AxiomMath/Stacks proves one. The Albanese property is proved, over every field and every genus, by
the Lean library of [frenzymath/Jacobian-Challenge](https://github.com/frenzymath/Jacobian-Challenge)
(Axel Delaval, Jie Xu, Shitan Xu; Apache-2.0; a solution of Kevin Buzzard's Jacobian challenge),
vendored here under `Jacobian/`:

* `AlgebraicGeometry.exists_abelianVariety_picardDegreeZero` (`Picard/FieldDescent.lean`): `Pic⁰` of a
  smooth proper geometrically integral curve is represented by an abelian variety;
* `AlgebraicGeometry.Curve.isAlbanese_abelJacobiMap` (`Curve/Albanese.lean`): the Abel–Jacobi map has
  the Albanese property (Milne, *Jacobian varieties*, Prop. 6.1);
* `AlgebraicGeometry.IsAlbanese.existsUnique_schemeMap` and
  `AlgebraicGeometry.isMonHom_of_isProper_of_geometricallyIntegral` (rigidity).

The bridge (`JacobianExists.lean`) only translates the hypotheses: the source's curves are
geometrically irreducible, the statement's geometrically connected (a smooth geometrically
connected morphism is geometrically integral: vendored Tau Ceti
`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`, already in the kernel); the source's
abelian varieties (commutative group object, smooth, proper, geometrically irreducible) are the
statement's `PkgI3.AbVar` (group object, proper, smooth, geometrically integral) on the same group
scheme.

## H-80: the normal model of a function field

`X` is Mathlib's relative normalization (Stacks 035H) of `ℙ¹_ℚ = Proj ℚ[X₀, X₁]` (the vendored
`AlgebraicGeometry.projectiveLine`, proper and integral, with charts `Γ ≅ ℚ[X]`) in `Spec F`, along
`Spec F ⟶ ℙ¹_ℚ` through the generic point (`K(ℙ¹) ≅ ℚ(T) ⊆ F`). Over each chart the integral closure
of `ℚ[X]` in `F` is finite (`IsIntegralClosure.finite`, characteristic `0`), so the normalization
map is finite and `X/ℚ` is proper; `X` is integral, its sections over the chart preimages are
integral closures in `F` (integrally closed), so its stalks are integrally closed; it has
dimension `dim ℙ¹ = 1` (integral surjective map, `ZInQ.Contrib.Dim`), and function field `F`.

## Vendored code: provenance and changes

* Source: `frenzymath/Jacobian-Challenge`, commit `c4254cce15b3e284a0a3ae1d73936f2ee195d272`
  (2026-11-06), pinned upstream to Lean `v4.35.0-rc3` / Mathlib
  `b63f6e8a68d220e3b3bc4f3792bb53650d375f24` (an ancestor of this repository's Mathlib
  `56a005855ea17e0b0958f73ec801ae140b0a1679`, 402 commits older). Copied: the import closure of
  `Jacobian.AlgebraicGeometry.Curve.Albanese`, `….Picard.FieldDescent`, `….Group.Rigidity` and
  `….AbelianVariety.Albanese.UniversalProperty`, 711 files. `LICENSE` (Apache-2.0) is copied
  unchanged; `NOTICE` reproduces the upstream NOTICE and lists the changes.
* Every copied file starts with a three-line comment naming the source module and commit, the
  copyright and the change (module paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`).
* Renaming (47 files): the 21 constants `AlgebraicGeometry.baseChangeDiagram*`,
  `baseChangeDiagramπ*`, `baseChangeDiagramStructure*`, `baseChangeCone*`, `baseChangeMap`,
  `baseChangeMap_id`, `_comp`, `_fst`, `_snd` are moved into `AlgebraicGeometry.JacobianChallenge`,
  because the vendored Stacks files of `Contrib/CloudW01Spread` declare different constants with the
  same names. The references were located from Lean's own `.ilean` reference data (local binders
  named `baseChangeMap` are left alone).
* Proof edits for the newer Mathlib (5 files, each marked `-- CloudW07 edit:`; Mathlib PR #43759
  made `CategoryTheory.End` a one-field structure, so endomorphisms are wrapped with `End.of` and
  applied with `.asHom`): `Algebra/Category/ModuleCat/Presheaf/InternalHom.lean`
  (`sectionsSMulHom`), `Algebra/Homology/DerivedCategory/Ext/BaseChange.lean` (actions
  `A →+* End F` applied through `.asHom`; two definitional helper lemmas),
  `AlgebraicGeometry/Cohomology/Basic.lean` (`smulPresheafHom`),
  `AlgebraicGeometry/Cohomology/FlatBaseChange.lean` (`smulRingHom`, `pushforwardSmulRingHom` and
  three statements), `AlgebraicGeometry/Hilbert/SectionPencil/BaseChange.lean` (one `change`).

## Build

```sh
lake build ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists \
  ZInQKernel.Contrib.CloudW07JacobiansCurves.NormalModel \
  ZInQKernel.Contrib.CloudW07JacobiansCurves.Checks
```

With the Mathlib cache this compiles the 711 vendored modules (about 25 minutes with four
single-threaded compilers on the fleet host; peak compiler RSS about 5 GB each) and three new
modules (`ZInQKernel.Contrib.Dim.{Basic,IntegralHom}` are existing kernel modules).
