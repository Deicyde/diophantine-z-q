# Scope and sizing

- **VERIFIED (source, before build).** The target at base 06e5d5d8 is
  `HDec.CMBranch.CMjBridges.CMPeriodShortWeierstrassComparison` in
  `ZInQKernel/Contrib/OneProof/JDescent.lean`. It asks for sections on the
  actual abelian variety over its number field and evaluations along a witness
  of the specified period.
- **VERIFIED (source).** The vendored
  `AlgebraicGeometry.SmoothProperCurve.exists_curveModel_riemannRoch_of_isAlgClosed`
  returns a curve model of an algebraically closed fibre and a divisor formula
  with an unspecified genus. Tau Ceti has Riemann–Roch for abstract function
  fields, and its `AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Genus.lean`
  computes the spaces at infinity and genus for a given nonsingular Weierstrass
  equation over the ground field. Neither result supplies the pole spaces at
  the identity of the given dimension-one `PkgI3.AbVar L`. No such bridge was
  found in the vendored curve or Jacobian development.
- **VERIFIED (source).** The projective coherent GAGA interface
  `ComplexAnalytic.gaga₁` compares cohomology of a supplied coherent sheaf on
  a supplied projective complex scheme. The uniformization supplies
  holomorphy of pulled-back regular sections on their domains; the stronger
  uniformization supplies local coordinates and openness. No declaration was
  found that supplies the two sections over L or takes a divisor supported on
  the identity to analytic pole bounds along `IsPeriodAt`.
- **VERIFIED (source).** Mathlib supplies the normalized Laurent principal part
  of ℘, holomorphy off the lattice, periodicity, its short cubic identity, and
  bounded entire rigidity. The vendored complex Weierstrass point
  parametrization gives surjectivity on affine points. These apply to the
  specified period pair, independently of any choice of equation over L.
- **SPECULATIVE (scope).** Constructing the required algebraic sections over L
  is a separate curve development: construct the low pole filtration on the
  actual scheme, prove its genus and the dimension formula over L (or prove
  base change and descend), and relate the identity parameter to evaluation.
  The useful local interface is a short nonsingular cubic over L on an open
  containing all the nonidentity points of the period map, with an even
  x-coordinate having an exact double pole there. Matching y may be deduced
  from nonsingularity and the cubic, without a separate pole bound for y.
- **VERIFIED (manuscript).** At L579 and L583–587 the input is a CM elliptic
  curve over L, and the degree of its j is used to bound the class number.
  The supplied reading of Fowler §2·1 is for the modular j of the period.
  The standard comparison is implicit; no manuscript error was identified.

- **VERIFIED (source refinement).** Tau Ceti's
  `Divisor.dim_natCast_zsmul_ofPoint_of_genus_eq_one`
  (`FieldTheory/FunctionField/Consequences/HighDegree.lean` in the vendored
  tree) is the exact dimension ladder. Its inputs are an abstract
  `IsFunctionField`, exact constants, genus one, and a place; it gives
  `dim L(nP) = n * deg P` for positive n. The missing inputs on the actual
  curve are the function-field and identity-place dictionary, and the
  genus-one verification for that field. The formula itself needs no new proof.
- **VERIFIED (source).** The stronger uniformization's local coordinate
  condition is on a chart obtained for that stronger uniformization, while the
  period in the row is specified by the weaker `LeafPush2.IsUniformization`.
  A proof using an algebraic local parameter must check its first-order
  effect along a witness of the given period, not along a newly chosen,
  unrelated lattice.

# Analytic reduction and preview

- **VERIFIED (Lean).** `JDescent2Analytic.lean` proves
  `hasDoublePoleAtZero_of_localParameter` and
  `shortCubic_coordinates_of_doublePole`. After subtracting the leading
  double-pole term from the even coordinate, periodicity and Liouville give
  an affine expression in ℘. Differentiating the evaluated cubic at its
  simple roots identifies its monic version with the lattice cubic. This
  fixes the constant in the affine expression, and the identity theorem
  gives one sign for the second coordinate. No pole condition on y is used.
  The four analytic theorems have only the three standard axioms.
- **VERIFIED (read-only).** The copied-and-retargeted Fowler spec ran with
  `--dry-run` only. It reports strict and strictest 4/25 -> 5/24 on 29 rows,
  conditional on a provider for `CMPeriodShortCoordinatesDoublePole`.
  Actual counts remain 4/25 in both classifications. The preview names a
  placeholder provider, with no declaration or fold for it.

# Scheme bridge and verification

- **VERIFIED (Lean).** `JDescent2.lean` compiles. It proves
  `shortWeierstrassComparison_of_doublePole` for the specified witness,
  `cmPeriodShortWeierstrassComparison_of_doublePole`, and
  `cmjDegree_of_print_of_doublePole`. The second theorem supplies the premise
  of the existing `cmPeriodJDescends_of_shortWeierstrassComparison`.
- **VERIFIED (Lean).** Both modules were compiled serially under the Lake
  environment with a read-only dependency overlay from the exact base.
  `axioms-output.txt` records all eight new theorem audits. Each contains
  only `propext`, `Classical.choice`, and `Quot.sound`.
- **VERIFIED (live scan).** `Discharges.lean` compiled. The output matches
  `OpenResearchLeaves66.cmjDegree` with precisely
  `CMPeriodShortCoordinatesDoublePole` and `CMjDegreePrint` as premises of the
  new theorem. The first is still open glue. No error in the manuscript or
  supplied reading was found.
