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

## New proved fragments

The three Lean modules in this contribution compile under pinned Lean 4.35.0
and contain 12 public theorems:

- Rationality of every coefficient indexed by m with p not dividing m, at
  arbitrary nonzero levels, with no diamond-action premise.
- The complete coefficient conclusion when p is in the identity or negative
  identity residue class modulo N. The latter uses the actual −I diamond
  action, with scalar (−1)^k, not a rationality assumption.
- The complete conclusion at levels N = 1, 2, 3, 4, 6, for every good prime
  and every input form. The finite unit checks are closed kernel decisions.

These statements work at every integer weight; in these special cases k ≥ 2
is not required. Their residue/level restrictions are explicit.

**The full all-level target remains OPEN.** A special-case proof is not its
discharge. Non-sign diamond action still needs an arithmetic rationality
argument. This group-theoretic limitation is not a claim that every other
unit acts nonscalarly at every weight or that the other levels are impossible.

Do not use `diamondIntegralToRational_of_heckePrime` circularly: that existing
result derives diamond rationality from the very full Hecke leaf being proved.
No general Hecke or diamond-preservation premise is hidden in these fragments.

## Checks and history

See `CHECKS.md` for actual build commands, the one coercion repair, the finite
kernel-context repair, and the 12-theorem transitive axiom audit. The audit has
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
Independent mathematical source review is separate from compiler checking.

Only new contribution files are added. Existing source, dependency pins,
assemblies and published proof history remain untouched. No PR, merge or
land is claimed by this WIP branch.

This contribution is an AI-assisted mathematical proof attempt. Compiled
fragments, source review and an integrated proof are different evidence grades.
It does not prove that Z is Diophantine in Q.
