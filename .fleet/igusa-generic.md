# igusa-generic — T28 on the generic locus: proved (and with igusa-special, T28 closed)

**Main result.** `T28.separationGeneric : T28.SeparationGeneric` (ZInQKernel/Contrib/T28/Mestre.lean).
Over an algebraically closed field of characteristic 0: if `J10 f ≠ 0`, `J10 g ≠ 0`,
`det (Matrix.of (PkgI1.yv f)) ≠ 0` (Clebsch's quadratic covariants independent = generic locus
`T28.GenericLocus`) and `J2, J4, J6, J10` of `f, g` agree, then `g = sexticAct f M e` with
`det M ≠ 0`, `e ≠ 0`. `#print axioms`: [propext, Classical.choice, Quot.sound].

Combined with igusa-special's `T28Special.separationBothSpecial` (merged here), T28 is proved:
`scratch/igusa-generic/t28_check.lean` checks
`T28.igusaClebschSeparation_of_bothSpecial T28Special.separationBothSpecial : PkgI1.IgusaClebschSeparation`
and `T28.igusaClebschSeparation_proved` (igusa-special's Assemble.lean); both have the standard
three axioms only (VERIFIED).

**How.** The M3 identities (Gram matrix of `yv` and `p6 f (yᵢyⱼyₖ)` are polynomials in the J's;
8 of 16 were still open, `ring` in 7 variables fails) are proved at every `f` with `J10 f ≠ 0`.
First, covariance of `yv`: translations by the derivation trick over `K[X]` with integer copies of
the covariants, swap and diagonal by `ring`, general matrices by Bruhat. Then the identities
transport along translation, swap and scaling. A normal form `x⁵+px³+qx²+rx+s` is reached via a
root (`IsAlgClosed.exists_root`). On it all 16 identities are small `ring` goals (<1 min). Then
`PkgI1.mestre_abstract` finishes.

**What compiles** (`lake build`, no errors): ZInQKernel/Contrib/T28/Generic.lean (split
statements, agreed with igusa-special), Covariance.lean (63 s), Mestre.lean (75 s).

**Declarations proved** (namespace T28, all standard axioms): `separationGeneric`,
`m3Identities_of_J10`, `m3At_of_J10`, `yvCovariance : YvCovariance`, `yv_actC`, `det_yv_actC`,
`det_yv_sexticAct`, `sexticAct_symm`, `igusaSeparationEq_of_split`,
`igusaSeparationEq_of_generic_bothSpecial`, `igusaClebschSeparation_of_split`,
`igusaClebschSeparation_of_generic_bothSpecial`, `igusaClebschSeparation_of_specialLocus`,
`igusaClebschSeparation_of_bothSpecial`, `genericLocus_iff_gramJ`, `genericLocus_congr`,
`separationBothSpecial_iff`, `separationSpecialLocus_iff`.

**What remains.** Nothing for T28. Notes: sympy/PARI are absent on this host (`~/pyenv` does not
exist), so the identity checks use a pure-python exact polynomial library
(scratch/igusa-generic/poly.py, nf_check.py, cov_check.py). Details are in
docs/research/igusa-generic.md and the log is scratch/igusa-generic/log.md. Merged origin/main once
(6c225515) and origin/wip/igusa-special (through 2d7f26e2).
