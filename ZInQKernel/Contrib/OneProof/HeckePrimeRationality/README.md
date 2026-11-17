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
- Two-division torsion distribution follows from that actual identity.
  The raw statement requires an admissible image; a separately defined zero
  extension gives the statement for every integer label. It is n=2 only.
- Mathlib's actual `(1,τ)` Weierstrass function is identified off its lattice
  with `−(H'/H)' + H'''(0)/(3H'(0))`. The poles are analytically cancelled
  and the finite-part normalization is proved, not assumed.
- Direct completed-theta Frobenius–Stickelberger addition is proved on its
  nonzero-denominator domain, with the actual derivative-defined finite part.
  It does not establish Eisenstein membership of the quadratic defect.

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
The analytic constructions above do not substitute for its proof. Genuine
Eisenstein identification, torsion Fourier duality, low-weight trace closure
and the spanning argument must still be bound to the actual forms.
The Γ₁ `(0,b)` family alone cannot replace the principal family.

The current 49-module audit checks 660 named public proofs/instances and
40 selected definitions with at most `propext`, `Classical.choice`,
`Quot.sound`, and no `sorryAx`. **Auditing a predicate's definition does not
prove that predicate**: `PrincipalProductSpanning` is still an input.
See `CHECKS.md` and `AnalyticAudit.lean` for exact editions and commands.
The earlier `Audit.lean` preserves the 34-module checkpoint.

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
