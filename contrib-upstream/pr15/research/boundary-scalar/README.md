# Boundary-scalar determinant comparison

This research extension computes the determinant discrepancy from the two
cross-boundary evaluations in an explicit common-strict presentation:

```math
\frac{\Phi_{\det}(\tau_F)}{\tau_S}=-\frac{q_F}{q_S}.
```

The Lean matrix proof derives full tensor/cofactor identities from normal-form
equations, actual cycles and closed functionals. A typed boundary--cup adapter
proves that the two specified adjunctions with a common normalization give equal
cross evaluations. **Proving those identities for the actual arithmetic
functionals remains open.**

Start here:

- [Complete derivation, assumptions and primitive negative example](DERIVATION.md)
- [Exact formal scope and arithmetic application contract](CONTRACT.md)
- [Verification results and source-to-formal crosswalk](VERIFICATION.md)
- [General Lean matrix theorem](../../lean/Research/BoundaryScalar.lean)
- [Typed Lean boundary--cup adapter](../../lean/Research/BoundaryCupAdapter.lean)
- [Supplied exact checker](check_boundary_scalar.py) and [received-source provenance](PROVENANCE.json)
- [Combined Open Math verification instructions](verification/README.md)

The supplied ZIP and pasted review are preserved unchanged in [inputs](inputs/).
Their review of `40d01c5` is historical; the supplied six-lemma Lean and Python
bytes match the branch at intake `083344e`. The supplied author reports helping
formulate the original candidate, so that report is an adversarial rereview.
A separately authored model review assesses this new contribution; its precise
role and limitations are recorded in the verification report.

The original [six-lemma packet](../determinant-switch/README.md), its 63-file
manifest and all earlier evidence remain intact. This extension changes no
manuscript, accepted helper module, main branch, dependency pin or arithmetic
acceptance record. The primitive example refutes a weaker local-data inference;
it is not a counterexample to the manuscript's arithmetic switch.

From the repository root, prepare the pinned dependencies' required import
closures, then use a fresh output directory for native local checking:

```sh
cd lean
MATHLIB_CACHE_DIR="$PWD/.checks/mathlib-cache-boundary-scalar" lake exe cache get \
  Mathlib.Algebra.Module.Equiv.Basic Mathlib.Tactic.Ring \
  Mathlib.LinearAlgebra.Matrix.Adjugate Mathlib.Tactic.FieldSimp \
  Mathlib.LinearAlgebra.BilinearForm.Properties
cd ..
python3 -B research/boundary-scalar/verify.py \
  --output lean/.checks/boundary-scalar-fresh
```

The checker verifies the received archive, original source guard and audit
history, exact finite models, all nine dependency pins, three fresh research
module compilations, and transitive axioms for the 21 selected declarations.
It performs no paranoid run. The independently reviewed algebraic bridge from
the common-strict matrices to the formal normal-form input remains ordinary
algebra; the precise boundary is documented in the contract and derivation.

The current cloud route is the repository-root [OPENMATH.md](../../OPENMATH.md).
It prepares a combined project with the old six declarations, thirteen principal
matrix declarations, and two adapter declarations. The challenge's intentional
proof holes are specifications in separate modules; solution proofs are checked
against the conventional axiom policy. The inherited default `ZInQ` target is
not the target for this contribution.
