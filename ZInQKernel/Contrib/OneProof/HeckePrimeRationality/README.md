# Prime Hecke rationality — proved low levels, open all-level target

## Exact original target

`CoeffRational.HeckePrimeIntegralToRational`, in
`ZInQKernel/Contrib/OneProof/CoeffRational.lean`, is unchanged. For every nonzero
level N, weight k ≥ 2, good prime p, and cusp form g on Γ₁(N) with integral
Fourier coefficients, it asks for rational coefficients of the actual
`heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g`.

**The original all-level target remains OPEN.** No global hypothesis has been
removed from the final single-proof assembly, and this work does not prove
that Z is Diophantine in Q.

## New closed level-five conclusion

`LevelFive.integral_input_hecke_rational` proves exactly the original contract
at N = 5, with only its original weight, prime, good-prime and integral-input
hypotheses. No generator, basis, Galois, dimension or rationality premise
remains in this export.

The proof also gives two stronger results at level five:

- Every diamond class preserves rational modular-form coefficients at every
  natural weight.
- The actual prime-Hecke operator preserves rational cusp-form coefficients
  at every nonnegative integer weight, including the bad prime.

With the earlier sign-only cases, `integral_input_hecke_rational_le_six`
proves the exact original conclusion at every nonzero level N ≤ 6. That level
bound is explicit; levels N ≥ 7 are not discharged.

## What was constructed, not assumed

1. Global nonvanishing of Mathlib's actual theta function at shifted nonzero
   5-torsion points, proved by transformations and dominant-term estimates.
2. Actual weight-one modular forms from completed theta logarithmic derivatives,
   with holomorphy, Γ₁ invariance and boundedness at every cusp proved.
3. Their actual q-expansions, cyclotomic coefficient membership and Galois
   covariance, including the constant and first coefficients.
4. Finite Galois structure and the fixed-field theorem for the explicit fifth
   cyclotomic field.
5. Concrete normalized generators A and B. Their rational coefficients follow
   from Galois conjugation and the sharp weight-one coefficient bound. The
   actual non-sign diamond has the integer matrix
   `⟨2⟩A = -3A - B`, `⟨2⟩B = 10A + 3B`.
6. The all-weight power basis and rational coordinate extraction, from a proved
   sharp level-five bound. The Hecke recurrence then gives the closed export.

The separate all-level conjugation result preserves real coefficients, not
rational coefficients. Neither it nor the level-five construction supplies
a uniform proof at arbitrary levels. No non-scalarity or impossibility claim
is made for other levels or weights.

## Checks, scope and history

See `CHECKS.md` for source hashes, commands, literal target checks and the
transitive axiom audits. The new source was compiled with pinned Lean 4.35.0
and independently reviewed. Audited closures use only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. Warm imports are
explicitly disclosed; this is not an independent cold replay of every
imported constant or a full-project integration certificate.

All source additions are confined to this contribution. Existing proof source,
dependency pins, assemblies and published history are preserved. Only this
contribution's status/check documents are updated additively. No PR, merge or
land is claimed by the WIP branch.

This is background work for the modularity/coefficient-field passage in the
manuscript's six-contact height estimate, not its pole-completeness argument.
The modular level N = 5 here is not the manuscript's coefficient prime ℓ = 5.
The all-level leaf and the other global proof obligations remain separate.

This is an AI-assisted mathematical proof contribution.
