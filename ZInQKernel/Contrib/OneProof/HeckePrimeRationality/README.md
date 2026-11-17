# Prime Hecke rationality — mathematical proof attempt

## Exact open target

`CoeffRational.HeckePrimeIntegralToRational`, declared in
`ZInQKernel/Contrib/OneProof/CoeffRational.lean` at base
`27657ffb10fd6706595d384eb412cfe5d091427d`.

For every nonzero level N, weight k ≥ 2, prime p not dividing N, and cusp form
g on Γ₁(N) with integral Fourier coefficients, prove that the actual
`heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g` has rational coefficients.
The original definition, operator, normalization, coefficient map and
quantifiers remain unchanged.

## Verified mathematical contributions

Six proof modules contain 51 public theorem/lemma declarations, compiled and
audited with pinned Lean 4.35.0. Their conclusions have different scopes:

- **Rationality fragments:** all coefficients off multiples of p at every
  nonzero level; all coefficients for p ≡ ±1 modulo N; and the complete
  conclusion at N = 1, 2, 3, 4, 6 for every good prime and every input form.
- **All-level conjugation:** every actual diamond class commutes with complex
  conjugation and preserves real Fourier coefficients. The actual good-prime
  Hecke operator preserves real coefficients too. Real is not rational.
- **Global theta nonvanishing:** Mathlib's actual `jacobiTheta₂` is nonzero at
  `(aτ+b)/5 + (τ+1)/2` for every τ in the upper half-plane whenever a and b
  are not both divisible by 5. No product formula or assumed zero set is used.
- **Sharp level-five coefficient bound:** for every integer k ≥ 0, an actual
  modular form on Γ₁(5) whose coefficients 0 through k vanish is zero. The
  proof constructs `f²(⟨2⟩f)²` on Γ₀(5) and uses its index-six Sturm bound.
  No basis, dimension or rationality premise is supplied. This theorem is
  on modular forms; applying it to cusp forms requires the standard coercion.

The rationality fragments and conjugation results work at every integer
weight; their level/residue/input-field restrictions remain explicit.

**The full all-level target remains OPEN.** The theta and sharp-bound lemmas
close two concrete analytic sub-obligations for a level-five construction;
they do not yet construct the weight-one modular forms, establish their
coefficient descent, or prove Hecke rationality at level five. They are not
being counted as a full leaf discharge.

The general non-sign diamond action still needs an arithmetic rationality
argument. Neither finite unit enumeration nor preservation of real
coefficients supplies it. No impossibility or universal non-scalarity claim
is made for other levels or weights.

Do not use `diamondIntegralToRational_of_heckePrime` circularly: that existing
result derives diamond rationality from the very full Hecke leaf being proved.
No general Hecke or diamond-preservation premise is hidden in these proofs.

## Checks and history

See `CHECKS.md` for build commands, source hashes, actual compiler repairs and
literal target checks. The combined 51-declaration transitive axiom audit uses
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
Separate mathematical source reviews checked the final code and its scope.
These checks are not an independent cold replay of every imported constant.

Only contribution additions and additive status updates are made. Existing
proof source, dependency pins, assemblies and published history are preserved.
No assumption has been removed from the final single-proof assembly, and no
PR, merge or land is claimed by this WIP branch.

This is an AI-assisted mathematical proof attempt. It does not prove that
Z is Diophantine in Q.
