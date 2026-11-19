# Results

- VERIFIED (repository, before Lean): clean base `88065599dcab27261058c3818897a083e570c434`.
  The live `OpenResearchLeaves66.cmjDegree` is GLUE in both counts. The preceding dry run
  projects 4 LEAF / 25 GLUE to 5 LEAF / 24 GLUE on the 29 H rows, conditional on j descent.
- VERIFIED (manuscript): L584–587 use the j-invariant of the same `E/L` obtained from the
  matrix units and the discriminant of its full geometric endomorphism order. The step
  uses the field of definition, not merely algebraicity of the analytic j over ℚ.
  STANDARD (exact locator from the supplied reading): Fowler §2·1, pp. 612–613 describes
  the primitive quadratic discriminant and supplies the degree equality. No fresh source reading.
- VERIFIED (scheme interfaces): `PkgI3.AbVar` carries a smooth, proper, geometrically
  integral group scheme and its dimension. `IsPeriodAt` carries a point map into that scheme
  with a scaled period lattice and the holomorphic pullback of regular functions. The stronger
  `BPAnalytic.Uniformization.IsUniformization` also gives local coordinates and openness.
  Both constrain pullback of already supplied sections; neither supplies global Weierstrass
  coordinates on the punctured curve over L.
- VERIFIED (equation interfaces): Mathlib's algebraic j and its variable-change and
  base-change lemmas start from coefficients. The allowed vendored `PeriodPair` theory gives
  the analytic ℘/℘′ equation and a surjective point parametrization of that equation. Its
  theorem realizing any complex Weierstrass equation from a lattice selects its own period
  pair and does not mention `E/L` or the period in `IsPeriodAt`.
- VERIFIED (library search): the tree includes projective coherent GAGA and `GAGAMorphism`
  for maps between abelian varieties. The latter takes two already constructed scheme
  abelian varieties. Neither it nor the function-field genus or Riemann–Roch interfaces
  located in Tau Ceti directly gives a Weierstrass model of the given scheme over L.
  No allowed declaration was found identifying the given scheme's lattice with the ℘
  coordinates of an equation over L.
- SPECULATIVE (size): the full Weierstrass route needs regular functions with pole orders
  2 and 3 at the identity over L, a cubic relation, and identification up to scaling via
  the complex uniformization. This is a separate development: genus-one pole spaces (for
  example using coherent GAGA over ℂ plus base change of sections back to L), construction
  and normalization of the coordinates, and identification via principal parts on the
  torus. An automorphism of ℂ fixing σ(L) acts on the scheme's points semilinearly; continuity
  or holomorphicity for arbitrary such automorphisms is not supplied and cannot be assumed.
  The fixed-field route would still need an algebraic realization of the analytic j.
- SCOPE: isolate the short Weierstrass coordinate comparison on the actual punctured scheme.
  Supply an L-equation and its regular coordinates with their evaluations along the period
  map, up to the usual nonzero weights 2 and 3. The lattice equation then determines the two
  complex coefficients, and the weights cancel out of j. Prove this last implication and the
  conditional row; stop before developing the missing comparison. No new literature leaf.
- VERIFIED (library follow-up): the vendored smooth proper curve bridge gives a
  function-field Riemann–Roch formula over an algebraically closed field, with an
  unspecified genus parameter. The section base-change theorem found alongside it
  is for global regular functions under its finite-map data. Neither supplies the
  controlled pole coordinates and their comparison required here.
- VERIFIED (Lean): the same-base compiled dependencies were available locally.
  `JDescent.lean` compiled with `lake env lean`. Its pointwise comparison is in terms
  of actual sections, the normalized lattice, the actual period point map, and the
  section equation over L. Evaluation of constants along σ and surjectivity of ℘
  off the lattice are proved. The latter gives two evaluations determining the
  coefficients; Mathlib's variable-change and coefficient-map formulas then give j descent.
  All five declarations checked by `#print axioms` use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- VERIFIED (source imports): the contribution's transitive import graph excludes
  the headline and the excluded library.
- VERIFIED (Lean): `lake env lean scratch/j-descent/Discharges.lean` reports
  33 open headline hypotheses. The new candidate matches `OpenResearchLeaves66.cmjDegree`
  with exactly `CMPeriodShortWeierstrassComparison` and `CMjDegreePrint` still assumed;
  it uses only the standard axioms.
- VERIFIED (dry run): the copied and updated spec ran with `--dry-run` only.
  The counts are 4 LEAF / 25 GLUE now and would be 5 LEAF / 24 GLUE in both
  strict and strictest with a provider for the comparison. Its proof name is a
  placeholder in the preview. No changes to the live statements, files, or counts.
