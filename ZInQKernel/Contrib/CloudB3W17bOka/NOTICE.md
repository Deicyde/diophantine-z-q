# Oka source and feasibility-port notice

Source: https://github.com/chrisflav/oka at
`9a9fc315498d58484ac1abc9668548212eb7c1ff`.

The selected source files retain their upstream copyright, license and author
headers. The Apache License, Version 2.0, is copied unchanged as `LICENSE`.
The upstream authors named in the selected source include Yuichiro Hoshi,
Junnosuke Koizumi, Christian Merten and other authors identified per file.

This is a private, unpublished compatibility experiment, not a completed or
independently reviewed GAGA contribution. It contains the explicitly selected
288-module direct projective-GAGA/analytic-ideal/pullback union. Original source
and dependency manifests are preserved separately and are not modified.

## Mechanical parser changes

The 22 selected local/scoped parser declarations are removed. Their uses are
expanded to ordinary terms, with an exact transformation manifest:

- 188 restriction-operator expansions to `TopCat.Presheaf.restrictOpen` or
  `modRes`, preserving the original `by order` proof;
- 43 `Γᵧ(...)` expansions to `Y.presheaf.obj (op ...)`;
- 224 projective-space notation expansions to
  `AlgebraicGeometry.ProjectiveSpace`;
- 182 local identifier-alias expansions (homogeneous polynomial grading,
  affine TopCat, and glue data).

Documentation immediately attached to a removed parser declaration is retained
as an ordinary comment. The notation-only `quotPrecheck` wrapper is removed.
No replacement syntax, notation, macro or elaborator is introduced.

## Proof/API changes currently under test

- `LocalOkaRing`: five proof-only Mathlib API adaptations (three
  `prod_le_prod₀`, one `prod_le_one₀`, one polynomial-first coefficient use).
- `Sheaf/PushforwardContinuous`: explicit construction of the existing right
  adjoint via a let-bound identity sheaf morphism, the presheaf
  `pullbackObjIsDefined_eq_top` theorem, and the sheaf pullback adjunction;
  the original theorem premises are unchanged.
- `ModuleCat/Stalk`: definition-local backward-elaboration transparency options
  restore elaboration of germ scalar multiplication over intersections of opens.
- `Ext/MapNatTrans`: explicit import of the current module defining
  `ShortComplex.exact_cokernel`; the lemma is not renamed or assumed.

Further compiler failures and edits are recorded separately. No successful full
GAGA build, all-declaration axiom census, H-105 discharge, pushed-head rebuild,
public submission or review is asserted by this notice.
