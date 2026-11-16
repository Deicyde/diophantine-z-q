# Heights: supporting results and the remaining proof boundary

This is a partial contribution. It closes **none** of `bostLowerBound`,
`javanpeykarBound`, or `pazukiCor13Upper`. Their exact definitions in
`ZInQKernel/OneProof/H/TailY.lean` are unchanged. No new published leaf or
other hypothesis is introduced.

`ZInQKernel/Contrib/OneProof/HeightSupport.lean` collects four small modules:

- `CloudB3SC4HeightSanity/UnboundedHodgeData.lean`: raw `HodgeData` with the
  existing rational integral and Gaussian period lattices can have every real
  height. This is **not** a counterexample to Bost: `MetrizedModel.arch` pins
  coefficients to the Jacobian of an analytic uniformization.
- `CloudB3SC4Bost/NormalizationBoundary.lean`: the exact Deligne/Faltings
  logarithmic equivalence, a positive gap between the exact and coarse
  constants, a scalar non-reversal example, and coefficient pinning with the
  **same** uniformization. The scalar example is not an abelian variety.
- `CloudB3SC4Javanpeykar/ArithmeticEndpoint.lean`: a finite real group-model
  height implies a genuine metrization exists; one bounded metrization gives
  an upper bound without a uniqueness assumption; the printed scalar
  estimates combine to `12756061 * g * d^5`, below `13 * 10^6 * g * d^5`.
  No Arakelov point height or Wronskian norm is constructed.
- `CloudB3SC4Pazuki/HeightNormalization.lean`: the actual `Char2` has sixteen
  coordinates, and the Euclidean height has the standard infinite-place
  multiplicities, finite-place maxima and division by the number-field degree.

There are seventeen closed helper theorems and one coefficient-rescaling
construction. They are supporting results, not seventeen open-statement
proofs. All use the unchanged repository and Mathlib definitions; no third-party
proof file is vendored.

## Printed-source findings

These are AI source readings, not human reading decisions. No reading flag or
classification file is changed.

- **Bost.** Bourbaki 795, Astérisque 237 (1996), p. 118, display (2.4), uses
  Deligne's metric. Theorem 2.1(i), p. 119, states existence of a
  dimension-dependent lower bound. The exact convenient all-abelian-variety
  inequality used by the target is printed in Gaudron–Rémond, *Théorème des
  périodes et degrés minimaux d'isogénies*, arXiv:1105.1230v1, Corollary 8.4,
  p. 37, with the height normalization in section 2.3, pp. 6–7. This corrects
  the locator, not the Lean statement.
- **Javanpeykar.** *Algebra & Number Theory* 8:1 (2014), Theorem 2.4.1,
  pp. 99–100; Theorem 4.5.2, pp. 122–123; and Proposition 3.5.1 as used in
  section 4.6, p. 123, supply the scalar inputs checked here. Their geometric
  and Arakelov hypotheses are not supplied by the scalar calculation.
- **Pazuki.** *Bulletin de la Société Mathématique de France* 140 (2012),
  Corollary 1.3(2), pp. 21–22; Definition 2.1, p. 26; and section 2.3.4 /
  Definition 2.6, pp. 30–31, confirm Euclidean/Fubini–Study height on all
  sixteen full half-characteristic theta constants and the Deligne shift.
  The suspected replacement by four second-order constants is not the
  printed definition: no `+ log 4` repair is justified by that suspicion.

## What still prevents closure

- Bost needs the arithmetic theta/cubist Moret–Bailly machinery and the genuine
  slope/evaluation estimate; Jensen's inequality or metric positivity alone
  does not provide it. Existing height dictionaries still assume the inequality.
- Javanpeykar needs canonical Arakelov point heights, Green/admissible metrics,
  the non-Weierstrass-point and Wronskian bounds, and their comparison with the
  Jacobian Hodge determinant. The five scalar/infimum helpers do not construct
  those objects or prove those bounds.
- Pazuki needs the theta–Faltings comparison and algebraization/descent of the
  analytic principal polarization used by the actual consumer. The existing
  conditional dictionary leaves those inputs open and raises the glue count
  against this base's leaf classification, so it is not presented as a closure.

No vacuity or counterexample abelian variety was established for an original
field. Searches found no complete supplier in the explicitly surveyed source
revisions; this is not a claim about every public Lean repository.

## Verification and scope

The fixed toolchain is Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Native defining-source and
statement/axiom checks are recorded separately from the prescribed Main /
`#discharges` check. The PR records the actual final outputs and review scope.
All source files are additions; no existing module, target, pin, ledger or
assembly is modified. There is no Main import in the contribution and no new
build-time command, parser, notation, elaborator, axiom or proof admission.

AI-assisted proof development and independent AI source/native review are
separate from human acceptance and merge authorization. A private evidence
bundle is available to the maintainer. No merge, fold or landing is requested.
