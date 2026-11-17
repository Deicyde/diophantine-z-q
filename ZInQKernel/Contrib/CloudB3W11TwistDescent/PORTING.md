# W11 Tate ports and integration notes

Source repository: https://github.com/anthropics/fermats-last-theorem
Pinned source commit: `6e837e75355538c7f80bab5b956861e86c4eacc2`.
Source toolchain: Lean `v4.33.1`, Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
Destination toolchain: Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The source's Apache-2.0 LICENSE and original NOTICE are preserved in the port
folders. The source's file-by-file attribution is also preserved in the trace
folder; individual file headers identify the reused source and modifications.
No original root notice or existing module was edited.

## Reused mathematics

- The 489-line Ax approximation argument: Hasse derivatives, polynomial-root
  estimates, Lucas/Kummer binomial valuations, degree descent, uniform constant
  `p²`. The port lives in `CloudB3W11AxEstimate/AxApprox.lean`.
- The intrinsic completion action API: `Def_PadicComplex_GaloisAction.lean`,
  ported in `CloudB3W11AxCompletion/GaloisAction.lean`; the unrelated Qbar/global
  Galois transport was omitted. Equality with the repository's `cpAct` is proved.
- The pure cyclotomic tower and degree/step arguments: ported in
  `CloudB3W11Cyclotomic/TowerDefinition.lean` and `TowerDegree.lean`. The
  irreducibility step reuses the repository's already vendored
  `TauCeti.irreducible_cyclotomic_prime_pow_ratPadic` (Apache-2.0), rather than
  duplicating the source's Eisenstein proof.
- The cyclic trace norm estimate, completion/trace construction, tensor
  character argument and whole-group local Tate vanishing: ported in the
  `CloudB3W11TateTrace` modules. `TraceComparison` identifies the constructed
  operator with genuine Mathlib normalized trace; `CyclotomicBounds` gives the
  unconditional pure-tower normalized-trace bounds.
- The finite-index twisted norm-product argument from the source's generic
  `S42C4` lemma: ported in this folder's `FiniteIndex.lean`.

## Removed implementation plumbing

Every new source avoids `P2M.Util`, the source's wrapper elaborators, and new
syntax/notation/macros/elaborators. Namespace/reactivation/export plumbing was
replaced by ordinary Lean declarations and explicit imports. Local notation
was expanded to actual types. Mathlib version drift was repaired with ordinary
proofs; the changed files document their source and modifications.

## New integration

The completion/density and finite-K closed-image bridge uses Mathlib infinite
Galois theory and the actual `cpAct`. `AxClosure` proves the arbitrary-K closure
form unconditionally from the ported Ax estimate.

`TateAdapter.lean` constructs the actual local cyclotomic character in `Cp`
units, proves its integer powers are exactly `cycPow`, rearranges the twist with
exponent `-i`, and applies the finite-index norm-product descent to the whole-G
Tate theorem. The final new files are:

- `Contrib/OneProof/AxSenTate.lean`:
  `ZInQ.Contrib.CloudB3W11.axSenTate_proof : ZInQ.Contrib.HodgeSplit.AxSenTate`.
- `Contrib/OneProof/TateTwistInvariants.lean`:
  `ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof : ZInQ.Contrib.HodgeSplit.TateTwistInvariants`.

Both exact theorem types and axiom lists have compiled. A closing claim is made
only with newest-main `#discharges` output and independent pushed-commit review.
The optional broader all-finite-K normalized-trace-bound Prop in early support
files remains unproved, but is **not used** by either closing proof. D's README
describes D's standalone algebraic/arithmetic edge; the complete Cp theorem
uses C's trace and the lead's finite-index adapter, not density of invariant
algebraic points.
