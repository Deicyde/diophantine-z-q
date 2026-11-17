# Prime Hecke rationality — low-level proof and unrestricted foundations

## Exact original target

`CoeffRational.HeckePrimeIntegralToRational`, in
`ZInQKernel/Contrib/OneProof/CoeffRational.lean`, is unchanged. For every nonzero
level N, weight k ≥ 2, good prime p, and cusp form g on Γ₁(N) with integral
Fourier coefficients, it asks for rational coefficients of the actual
`heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g`.

**The original all-level target remains OPEN.** No global hypothesis has been
removed from the final single-proof assembly. This work does not prove that
Z is Diophantine in Q.

## Closed low-level Hecke conclusion

`LevelFive.integral_input_hecke_rational` proves exactly the original contract
at N = 5, with only its original weight, prime, good-prime and integral-input
hypotheses. Its generators, rational coefficients, power basis and non-sign
diamond matrix are constructed, not assumed.

At level five, rational cusp-form input has rational prime-Hecke output at
all nonnegative integer weights, including the bad prime. With the earlier
sign cases, `integral_input_hecke_rational_le_six` proves the original
conclusion for every nonzero N ≤ 6. The level bound is explicit; no conclusion
for arbitrary input forms at N ≥ 7 is claimed.

## Verified arbitrary-level foundations

The new constructions cover every positive N, including even and composite
levels. They are not being counted as the original all-level leaf:

- **Theta nonvanishing:** the actual theta function is nonzero at
  `(aτ+b)/N + (τ+1)/2` whenever a and b are not both divisible by N. This uses
  a relative paired-series estimate, not an assumed product or zero set.
- **Actual modular forms:** completed torsion logarithmic derivatives yield
  weight-one forms on Γ₁(N) for `(0,b)`, and on Γ(N) for every admissible pair.
  All invariance, holomorphy and every-cusp boundedness fields are proved.
  Cusp constants depend on the level and label; the form need not be nonzero.
- **Actual coefficient arithmetic:** every admissible integer pair has a
  proved period-N expansion with coefficients in Q(exp(2πi/N)) and actual
  coefficientwise Galois covariance. The two sparse exponent branches are
  both retained at overlaps. This does not make each coefficient rational.
- **The completed theta function:** the actual entire function
  `H(z) = exp(πiz) theta(z + (τ+1)/2, τ)` has a proved derivative, quasi-periods,
  oddness and an exact expression for every Good torsion logarithmic
  derivative. Its global zero set, simple zeros and multiplication formula
  are not proved in that module.
- **The actual field:** cyclotomic structure, finite dimensionality, Galois
  structure and automorphism root selectors are proved for that same field.
- **Period conversion:** for Γ₁(N) forms, the period-N series is exactly
  `PowerSeries.expand N` of the width-one series. Index N·m corresponds to m;
  coefficients outside the multiples vanish. The two coefficient-field and
  rationality conditions are equivalent.
- **The invariant projector:** the explicit average `N⁻¹ ∑_{j<N} f | T^j` is
  an actual Γ₁(N) form, complex-linear, and the identity after restriction
  of Γ₁(N) forms. It transports a spanning family only if that family's
  principal-level spanning is already proved.
- **Residue transport:** the correcting Γ₁ matrix is explicit. Literal
  global commutation of the Galois label map with Γ₀ matrices is not asserted.
  A separate dictionary is proved only for the explicit `(0,b)` family.
- **Coordinates and conjugates:** one linear retraction recovers subfield
  coordinates from all Fourier rows simultaneously. Explicit finite-family
  conjugate data then constructs a unique actual coefficient-conjugate form;
  rational coefficients imply fixedness. These helpers neither supply the
  family data nor create a spanning representation.

The separate all-level complex-conjugation theorem preserves real
coefficients. Realness is not rationality. No arbitrary-level two-generator
power basis, non-scalarity assertion or impossibility claim is made.

## Remaining mathematical bridge

The unrestricted route needs the actual principal-level Eisenstein
product-spanning theorem and its binding to these exact theta forms, followed
by concrete invariant-space Galois/diamond compatibility. The classical
same-level spanning statement for N ≥ 3 and weight ≥ 2 is Khuri-Makdisi's
Theorem 5.1 in arXiv:0903.1439v6, combined with its generator theorem. Its
published proof is not a closed Lean proof in this contribution.

Principal-level spanning cannot be replaced by a claim about the `(0,b)`
family on Γ₁(N). Nor can an assumed spanning premise or finite-family
covariance be counted as a discharge of the original all-level leaf.
The full product and invariant-descent bindings remain separate work.

The zero-label control proves raw F(N,0,0) = 1/2 and F(N,N,0) = 3/2, with
explicit failures of naive raw two-division. Those excluded values are not
representative-independent. All-torsion distribution therefore needs a
separate zero extension on every bad label, or explicit omitted-point
corrections. The genuine Good-generator trace question is not falsified.

## Checks, scope and history

See `CHECKS.md` for exact source hashes, build commands, literal target checks
and axiom audits. The 34-module checkpoint audits 479 public proof/instance
declarations and ten actual constructions, using at most `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. Separate mathematical
source review checks the exact code and scopes. Warm imports are disclosed;
this is not an independent cold replay of every imported constant or a
full-project acceptance certificate.

Only contribution additions and this contribution's status/check updates are
made. Existing proof source, pins, assemblies and published history are
preserved. No PR, merge, land or global hypothesis discharge is claimed.

This remains H-decomposition background for the manuscript's six-contact
height estimate, not its pole-completeness/Route K lane. Modular level N = 5
is not the manuscript's coefficient prime ℓ = 5. The full Z-in-Q proof and
all other global obligations remain separate.

This is an AI-assisted mathematical proof contribution.
