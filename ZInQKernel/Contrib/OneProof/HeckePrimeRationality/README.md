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
- The correlation has constructive finite original-level row products,
  with determinant ±n, both slope congruences, and uncollected coefficients
  ±n. Exact signed quotient transport pulls both actual factors back to the
  original level. The explicit finite defect list is assembled into one
  actual weight-two correction form at (n−1)!M, with proved independent
  series-span membership. Every integer slope is covered by guarded integer
  residues; the rows and correction are fixed before the quantifier over τ.
  At M=nℓ the correction form has exactly level n!ℓ.
- Positive divisible levels have actual injective linear restriction maps
  on the independent series spans, with exact scaled-label images and
  factorial-level inclusions. The earlier normalized-trace partial alone
  does not give general lower-span closure.
- General lower-series-span trace closure is now proved for every positive
  N∣M and arbitrary upper labels. Genuine principal-group matrix moves,
  complete-fiber distribution and the unique coprime-prime zero point handle
  both repeated and coprime prime extensions. Invariant descent constructs
  an actual lower series-span form before using restriction injectivity.
  This is not trace closure of the whole principal-product ring.
- The actual Weierstrass derivative y=℘′ has an absolutely convergent
  weight-three inverse-cube series and a derived ordinary third kernel jet.
  Finite cubic inversion gives actual weight-three modular forms for every
  positive level and all integer labels, including the zero convention.
  At N ≥ 3 they belong to the genuine Good degree-three product span at
  the same level. No whole weight-three space is asserted to be spanned.
- Actual lattice invariants g₂ and g₃ are finite nonzero-torsion polynomials
  for N ≥ 2. Their modular forms lie in the same-level Good degree-four/six
  product spans for N ≥ 3. The true N²−1 count, critical WP′ zeros, excluded
  N=1 denominator and normalizations g₂=60G₄, g₃=140G₆ are proved. These are
  not the quasimodular weight-two G₂ or a whole-space generation statement.
- Embedded lower-level signed torsion correlations are actual weight-two
  forms on Γ(ℓ) for every positive n, integer slope and lower-level labels.
  For ℓ ≥ 3 they belong to the genuine Good degree-two product span. Their
  lower series correction is constructed through the proved trace descent,
  with all fields and both original-level row-factor pullbacks supplied.
- For p prime with p∣ℓ and ℓ ≥ 3, actual normalized trace of every Good
  degree-two product from pℓ to ℓ belongs to the lower product span. All
  ranks and p=2 are covered. This is the repeated-prime case only; it does
  not give the coprime-prime case or all-weight product-trace closure.
- For N ≥ 3 and every Nat weight k ≥ 3, the actual scaled unrestricted
  congruence-grid inverse-power series has a genuine weight-k form in the
  same-level Good length-k product span, for every integer label. Good
  rows use actual WP derivative expressions; bad even rows retain actual
  G_k by absolute residue-grid averaging. This is not an identification
  with the separate primitive gcd=1 Eisenstein series or whole-space span.
- For coprime prime p and N ≥ 3, actual normalized trace of every Good
  degree-two principal product, and every member of its genuine upper span,
  lies in the lower product span. Actual CRT splitting, negative-determinant
  Fourier orientation and nonempty orbit averaging cover all ranks and zero
  classes. No desired orbit identity or product-trace premise is supplied.
- For positive N∣M with N ≥ 3, actual normalized trace sends every upper
  degree-two product-span member to the lower product span. Prime extension
  and strong induction construct the lower member before restriction
  injectivity is used. Invariant upper members descend to actual lower forms
  in that same span. This is degree two only, not all-weight or whole-space
  principal-product spanning.
- For N ≥ 3 and Nat k ≥ 3, every actual Mathlib primitive gcd=1
  `eisensteinSeriesMF` lies in the same-level Good length-k product span.
  True signed gcd decomposition and inverse-unit residue permutations bind
  the primitive series to the unrestricted grid. An actual finite matrix
  inverse gives coefficients independent of τ; the grid form is divided by
  N^k. Nonprimitive primitive-series rows are proved zero, without erasing
  the unrelated bad even grid values G_k.
- The guarded permutation-convolution inverse is constructed from the
  actual tail bound ∑_{d≥2}d^(−k) ≤ 1/2 for k ≥ 3. Its sup-norm contraction
  has no finite-index cardinality loss. Identifying the full positive-index
  series additionally requires the stated identity and guard data at d=1.
- For N ≥ 3, positive N∣M and every Nat weight k ≥ 3, actual normalized
  trace preserves the span of independently defined all-label congruence
  series. The variable-weight trace, prime formulas, invariant descent and
  exact raw N^(−k) normalization are proved. This is a specific series span,
  not the full product span or the entire modular-form space.
- Actual rectangular theta isogenies give rational diagonal and inverse-
  diagonal transport of every Good homogeneous torsion-product span to a
  constructed common principal level. A proved positive rational matrix
  decomposition extends this to every positive-determinant A∈GL₂(Q), at
  M=D(A)N with D(A)>0 independent of N and the input form. The scalar
  factors are derived from the actual slash convention, including weight
  zero. All-label zero-extended identities have separately proved bad-fibre
  cancellation.
- Ordinary Weierstrass pole cancellation determines the finite cyclic x
  corrections in both rectangular directions. All-label x transport then
  gives actual diagonal and inverse-diagonal preservation of the independently
  generated mixed x_P λ_Q span, with exact weight-three factors 1/n and
  1/n². Bad shifted sums equal their cyclic corrections, not zero. Positive
  rational matrix decomposition extends actual mixed transport to arbitrary
  positive-determinant GL₂(Q), with M=D(A)N. The independently Good-generated
  mixed span is proved equal to the all-label lower mixed span. This neither
  identifies that span with all weight-three forms nor transports the extra
  class-series summand merely by this result.
- Every positive-level principal cusp form has an actual square-level
  Gamma-one carrier with exact period-matched expansion. Nonzero character
  and good-Hecke eigencomponents stay in the original finite positive-rational
  translate orbit. A minimal-positive-level argument, with actual nonzero
  adjoint lowering and center handling, then produces a genuine normalized
  newform at some 0<L≤N² in that same orbit. The first coefficient is proved
  nonzero before normalization; no newness or representation premise is
  supplied.
- Mixed weight-three addition and distribution retain the full derivative
  y=℘′, factor 1/2 and every degenerate class. Their series span is identified
  with the actual weight-three congruence-series span. For every prime p∣ℓ
  and ℓ≥3, every actual integer-labeled x_P λ_Q mixed form traces into the
  genuine lower Good degree-three product span. A constructed terminating
  integer-slope recursion supplies the earlier all-slope premise, with all
  higher-level series corrections and exact row divisions retained. This
  is repeated-prime mixed trace, not full weight-three spanning or trace
  of arbitrary degree-three products. The coprime-prime case is also proved,
  with actual CRT orbit sums and second-factor Fourier reduction. Combining
  these prime cases gives mixed-space trace and invariant descent for every
  positive N∣M with N≥3. The space is lower mixed forms plus class-series
  forms, not all homogeneous degree-three products.
- For N,k≥3, every actual primitive Eisenstein modular form is Petersson-
  orthogonal to every principal cusp form in both orientations. Actual
  measure, faithful principal fundamental domain, oriented primitive-row
  equivalence and absolute integrability are supplied before unfolding and
  Fubini. A separate explicit finite constant-term interpolation now proves
  primitive Eisenstein plus cusp decomposition for N,k≥3. The actual
  principal-domain positive self-pairing proves disjointness of the primitive
  span and cusp embedding range, hence complementarity and uniqueness of the
  residual cusp only; generator coefficients are not asserted unique.
- A new convergent second-theta-moment series determines the actual weight-
  two x constants. For every positive N and every integer label, including
  bad zero classes, the period-N q-expansion constant and every SL₂(Z) slash
  profile are proved. The axis value is −4π²w/(1−w)²−π²/3 and the non-axis
  value is −π²/3; denominators are proved nonzero on good axis labels.
  This profile theorem by itself is not a decomposition. Later actual
  one-dimensional inverse-square convolution, complete-coset trace zero and
  the finite 2N kernel construct division/product prototypes and an arbitrary
  weight-two decomposition f=E+g for N≥3. E lies in the division-series and
  Good degree-two product spans; g is a genuine same-level cusp form.
  Petersson orthogonality, directness and uniqueness at weight two are not
  proved by that construction.
- For every positive N and natural k≥3, actual absolute congruence-series
  spans have positive-rational GL₂ transport at a constructed level with a
  matrix-only multiplier. At weight three this also transports the full
  lower-mixed plus class-series space, using honest point and grid refinement
  to one common level. This is not whole M₃ spanning.
- Actual cusp×modular-form Petersson trace adjunction and positive-rational
  translate adjunction retain the faithful center quotient, genuine absolute
  integrability and the determinant factor det^(k−2). Given orthogonality to
  the actual mixed/cusp intersection, the produced weight-three decomposition
  extends it to all mixed tests. Positive-rational orthogonality against lower
  mixed test forms is then proved without a supplied test-transport premise.
- Actual twists have all-complex-exponent convergent Mellin identities and
  exact primitive Gauss/critical-integral factors. A separate normalized
  coefficient argument produces nonzero opposite-parity twist values only
  for Re(s)>k/2+1; at s=k−1 this covers k≥5, not critical weights two or three.
- Genuine principal modular-form tensor multiplication has a proved product
  range and analytic cancellation. An actual-field pole-section pencil kernel
  and nonspecial degree-gap theorem retain independent Riemann–Roch and
  finite-dimensionality inputs. The reduction to a gap supplier and the
  (2,2), (2,3), (3,3) maps does not discharge those inputs or identify the
  actual modular-curve/Hodge section spaces.

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
defect have proved membership in the independent convergent series span,
by explicit equalities and finite combinations. Their integer-slope canonical
correction and general lower-series-span trace closure are proved. This is
not identification with a classical Petersson-Eisenstein subspace or full
modular-form spanning. Degree-two all-level product trace, all-weight
congruence-series trace closure and primitive-series generator inclusion
are proved. Arbitrary positive rational homogeneous and mixed transport,
all-divisible mixed-space trace, normalized newform extraction and primitive
Petersson orthogonality, the N,k≥3 primitive Eisenstein/cusp complement,
weight-two additive division/product-plus-cusp decomposition and full mixed
rational transport are also proved. Actual weight-two Petersson orthogonality,
Rankin–Selberg product detection, critical weight-two/three special-value
nonvanishing, actual higher-weight multiplication and full principal spanning
remain separate. The Γ₁ `(0,b)` family alone cannot replace the principal
family.

The 217-module cumulative audit checks 2977 selected public source records.
Ten additional earlier literal-contract theorems give 2987 distinct audited
records, all with at most `propext`, `Classical.choice`, `Quot.sound`, and no
`sorryAx`. Component audit literals and generated structure projections are
recorded separately rather than silently counted as new mathematical source.
The full literal inventory includes private declarations and is not equated
with the selected public audit list.
**Auditing a predicate's definition does not prove that predicate**:
`PrincipalProductSpanning` is still an input.
See `CHECKS.md` and `PrincipalDecompositionTransportAudit.lean` for exact
editions and commands. Earlier audit editions preserve previous checkpoints.

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
