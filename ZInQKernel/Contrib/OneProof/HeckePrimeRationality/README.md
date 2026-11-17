# Prime Hecke rationality — mathematical proof attempt

## Exact target

`CoeffRational.HeckePrimeIntegralToRational`, as declared in
`ZInQKernel/Contrib/OneProof/CoeffRational.lean` at base
`27657ffb10fd6706595d384eb412cfe5d091427d`.

For every nonzero level N, weight k ≥ 2, prime p not dividing N, and cusp form
g on Γ₁(N) with all Fourier coefficients integral, prove that the actual
`heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g` has rational coefficients.
The original definition, operator, normalization, coefficient map and
quantifiers remain unchanged.

## Work in progress

This is a new mathematical proof attempt, not a completed discharge. The first
construction handles the identity-diamond class and coefficients off the
multiples of p. The full target still requires control of the nontrivial
diamond action on the rational/integral structure. No desired Hecke-rationality
or diamond-preservation assumption will be presented as a proof of the leaf.

Current status: target and recurrence read; new proof bodies under construction.
Compilation and independent verification of this contribution are not yet complete.
No `sorry`, added axiom, target weakening, or new kernel definition is intended.

Only new contribution files are added. Existing source, dependency pins,
assemblies, published proof history and other contributors' work stay untouched.
No merge or land has been performed.

## Boundaries

A checked special case or coefficient lemma does not close the all-level leaf.
An axiom report, source draft, successful build and integrated proof are
separate results. This attempt does not prove that Z is Diophantine in Q.
