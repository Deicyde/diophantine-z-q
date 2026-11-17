# Prime Hecke rationality — exact reduction and analytic producers

## Original target remains open

`CoeffRational.HeckePrimeIntegralToRational` is unchanged: every nonzero level,
integer weight k ≥ 2, good prime p and actual Γ₁(N) cusp form with integral
Fourier coefficients must have rational coefficients after the actual
`heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p)`.

**That unrestricted leaf is not proved.** No global hypothesis has been
removed from the final assembly, and this work does not prove that Z is
Diophantine in Q.

## Exact proved conclusions and reduction

The original conclusion is proved unconditionally for every nonzero N ≤ 6.
The N=5 proof constructs its rational generators, actual power basis and
non-sign diamond matrix; its endpoint has only the original hypotheses.
`integral_input_hecke_rational_le_six` retains the level bound explicitly.

For arbitrary positive N, the new finite-representation chain is proved:

1. A given finite complex representation of the actual Γ(N)-restriction in
   Good torsion-product forms admits one coefficient-field coordinate vector
   satisfying all Fourier rows simultaneously.
2. Actual Galois covariance and the corrected Γ₀ representative, acting on
   Γ₁ invariants, prove rationality of every actual diamond translate.
3. The guarded actual cusp-form recurrence proves rational prime-Hecke output,
   including the bad-prime zero branch. Its `m/p` term is used only under
   `p ∣ m`.

The representation is **not provided by these results**. The theorem
`heckePrimeIntegralToRational_of_principalProductSpanning` reduces the exact
original all-level, integer-weight leaf to the explicit unproved property
`PrincipalProductSpanning`. This property concerns actual principal-level
modular forms of weight at least two; it mentions no Hecke operator, diamond,
rationality or coefficient. Small levels and the nonnegative weight cast
are proved in the reduction, not hidden premises.

## Verified mathematical constructions

- Actual completed torsion logarithmic derivatives give Γ₁(N) and Γ(N)
  weight-one modular forms, with every invariance, holomorphy and cusp field
  proved. Arbitrary integer Good labels, even and composite levels are covered.
- Every actual period-N coefficient belongs to Q(exp(2πi/N)), with proved
  coefficientwise Galois covariance. Sparse branches are both retained at
  overlaps. The same field's finite/Galois/root-selector facts are proved.
- Exact Γ₁ period conversion gives `PowerSeries.expand N`: index N·m at
  period N corresponds to m at period one, and off-multiples vanish.
- The explicit unipotent average is an actual complex-linear Γ₁ projector.
  It transports a spanning family only when that family's spanning is proved.
- Homogeneous products are actual principal-level modular forms, with proved
  coefficient-field, Galois and full SL₂ covariance. No product-basis claim
  is made.
- The actual completed odd theta H has proved holomorphy, quasi-periods,
  global lattice zero set and simple origin zero. Its multiplication identity
  is proved for every positive division degree, including degree one and zeros.
- Torsion distribution follows from that actual identity in every positive
  degree. The raw statement requires an admissible image; the established
  zero extension gives the statement for every integer label. Only the full
  sum is asserted to vanish over a zero-class fiber, not each individual term.
- The intrinsic theta kernel gives actual torsion Fourier duality at every
  positive level: the normalizing factor is −1/N and the tau-first pairing
  exponent is `br−as`. Its poles are analytically cancelled; no Fourier or
  extension identity is assumed.
- Mathlib's actual `(1,τ)` Weierstrass function is identified off its lattice
  with `−(H'/H)' + H'''(0)/(3H'(0))`. The poles are analytically cancelled
  and the finite-part normalization is proved, not assumed.
- The actual finite-part constant equals `−EisensteinSeries.G2 τ`.
  Its transformation law, holomorphy and cusp boundedness are proved;
  the resulting level-one weight-two form vanishes by Mathlib's theorem.
  No triple-product identity or constant-identification premise is assumed.
  This identifies the single constant, not the torsion values as Eisenstein.
- Direct completed-theta Frobenius–Stickelberger addition is proved on its
  nonzero-denominator domain, with the actual derivative-defined finite part.
  Its concrete torsion consequence is also proved:
  `λP λQ − λP λS − λQ λS = −μP − μQ − μS` for three admissible labels
  `S = P + Q`. All integer-label cases are also stated, with the actual
  negative-square terms at zero classes. The three-μ formula is used only
  in the nondegenerate branch. None of this proves Eisenstein membership.
- Actual Weierstrass torsion values satisfy distribution in every positive
  degree, with factor n² and the explicit zero convention for bad labels.
  The full sum over nonzero n-torsion vanishes; no individual-value vanishing
  claim is made.
- The actual μ/x Fourier dualities are proved for every positive level and
  every integer label, with factors −1 and −1/N² and pairing exponent `br−as`.
  Their second Laurent coefficient comes from an ordinary analytic kernel
  unit. The zero row follows from the actual x-distribution and finite
  orthogonality, not a Fourier-defined replacement for μ or x.
- The actual μ-values satisfy all-degree distribution with factor 1,
  including a zero-class image. Frequency selection is an explicit bijection;
  no individual preimage value is forced to vanish.
- Actual x, λ and μ are bundled as principal-level modular forms of weights
  2, 1 and 2 for every positive N and every integer label. Invariance,
  holomorphy and every-cusp boundedness are proved, including N=1 and N=2.
- Actual x is identified with an independently defined, convergent
  principal-divisor weight-two Eisenstein lattice series. Absolute lattice
  differences and ordinarily summable rows are kept distinct; the raw
  two-dimensional inverse-square sum is not rearranged as an absolute sum.
  This is an identification in the series sense, not a Petersson-subspace
  or trace-closure theorem.
- For N ≥ 3, explicit quadratic Fourier inversion puts the actual x- and
  μ-forms in the complex span of genuine Good degree-two principal torsion
  products at the same level. The denominator N²−4 is proved nonzero under
  this visible bound; no such formula is claimed at N=2. This is generator
  inclusion, not spanning of the whole modular-form space.
- Actual finite correlations obey the exact recurrence, with the full
  defect correction and factors n/s and 1/s. An injective ambient-level map
  preserves actual values and constructs the needed preimage at a larger
  level. Slope reduction and a terminating Euclidean expansion are proved.
  Every larger-level defect remains explicit; original-level determinant
  constraints and label descent are not supplied by that expansion.
- Actual μ, λ² and every quadratic label case have proved membership in
  the independently defined division-series span. The normalized modular
  form evaluates exactly to the raw `reg` defect; finite correction sums
  remain at their stated ambient level. Zero/opposite cases retain negative
  squares, and the three-μ formula is restricted to three Good classes.
  No Petersson-subspace, level-descent or whole-space statement follows.
- The correlation now has constructive finite original-level row products,
  with determinant ±n, both slope congruences, and uncollected coefficients
  ±n. Signed quotient transport pulls both actual factors back to the
  original level. Each explicit D-correction level divides (n−1)!M, exactly
  the common n!ℓ bound when M=nℓ. The slope is natural; no arbitrary-field
  or integer-slope statement is silently substituted.
- Positive divisible levels have actual injective linear restriction maps
  on the independent series spans, with exact scaled-label images and
  factorial-level inclusions. The actual normalized trace descends upward
  images and scaled-generator combinations and preserves the upper span
  after restriction. Arbitrary lower-level series-span closure is not proved.
- The actual Weierstrass derivative y=℘′ has an absolutely convergent
  weight-three inverse-cube series and a derived ordinary third kernel jet.
  Finite cubic inversion gives actual weight-three modular forms for every
  positive level and all integer labels, including the zero convention.
  At N ≥ 3 they belong to the genuine Good degree-three product span at
  the same level. No whole weight-three space is asserted to be spanned.

Raw excluded labels are not representative-independent: the zero-label
control proves values 1/2 and 3/2 and refutes naive raw distribution. The
separate zero extension leaves all raw definitions and Good generators
unchanged. Its zero convention is not itself a proof of a Laurent finite part.

Real-coefficient preservation is also proved separately. Realness is not
rationality, and a non-sign unit does not force a nonscalar operator in every
space or weight.

## Remaining producer and verification boundary

The actual principal Eisenstein-product spanning theorem remains missing.
The classical source is Khuri-Makdisi, arXiv:0903.1439v6, Theorem 5.1 and its
generator theorem: same principal level N ≥ 3, weight ≥ 2, base field C.
The proved x-series identification, μ/x Fourier dualities and same-level
quadratic generator inclusion do not substitute for the spanning proof.
The μ-forms, every quadratic label case and the normalized raw correlation
defect now have proved membership in the independent convergent series span,
by explicit equalities and finite combinations. This is not identification
with a classical Petersson-Eisenstein subspace. Original-level row constraints
are proved for natural slopes. Binding their finite corrections to one form
at the canonical factorial level, signed-slope extension, general lower-level
series-span trace closure and the full spanning argument remain separate.
The Γ₁ `(0,b)` family alone cannot replace the principal family.

The current 81-module audit checks 1129 named public source proofs/instances,
146 selected definitions, structures or type aliases and one additional
capture of the derived row decision instance. All 1276 records have at most
`propext`, `Classical.choice`, `Quot.sound`, and no `sorryAx`. **Auditing a
predicate's definition does not prove that predicate**:
`PrincipalProductSpanning` is still an input.
See `CHECKS.md` and `WeightThreeAudit.lean` for exact editions and commands.
The seven earlier audit editions preserve the 34-, 49-, 56-, 59-, 71-, 73-
and 78-module checkpoints.

These are ordinary pinned compilations plus complete separate source reviews
with warm imports, not independent cold replay of all imported constants or
a full-project acceptance certificate. Existing mathematical source, pins,
assemblies and published history are preserved. No PR, merge or landing is
claimed.

This is H-decomposition background for the manuscript's six-contact height
estimate, not the pole-completeness/Route K lane. Modular level N=5 is not the
manuscript's coefficient prime ℓ=5. The full Z-in-Q theorem and other global
obligations remain separate.

This is an AI-assisted mathematical proof contribution.
