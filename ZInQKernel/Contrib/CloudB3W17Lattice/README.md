# W17: compact quotients and full lattices

Import `ZInQKernel.Contrib.CloudB3W17Lattice.CompactQuotient` (Mathlib only), or
`ZInQKernel.Contrib.CloudB3W17Lattice.TorusBridge` for the existing repository torus.

## Results

`span_top_of_compactSpace_quotient`: if the quotient of a finite-dimensional real
normed space `E` by a `ℤ`-submodule `Λ` is compact, then `Λ` spans `E` over `ℝ`.
**Discreteness is not needed.** With `[DiscreteTopology Λ]`,
`isZLattice_of_compactSpace_quotient` gives the exact `IsZLattice ℝ Λ` class.

The proof kills a proper span with a nonzero continuous scalar functional,
descends it to the compact quotient, and obtains the impossible compact image
`ℝ` by surjectivity of that functional.

Other proved suppliers:

- `liftKer` and its injectivity, surjectivity, continuity and openness;
- `quotientContinuousAddEquiv`: the quotient's topological-group isomorphism to
  the image of a continuous open surjective homomorphism with exact kernel;
- `discreteTopology_of_injOn`: injectivity on a neighborhood of zero makes the
  kernel discrete;
- `isZLattice_of_isOpenMap`: a discrete exact kernel of a continuous open
  surjective homomorphism onto a compact group is a full lattice;
- `isZLattice_iff_compactSpace_torus`: the reverse direction uses the existing
  `BPAnalytic.compactSpace_torus`, not a duplicate proof;
- `isZLattice_of_exp`: combines discreteness, fullness and a topological-group
  quotient isomorphism for a supplied open surjective map injective near zero.

These are partial infrastructure, not either universal H103/H105 field. The
exponential itself is not assumed to be available from Mathlib and is not
constructed **in these two files**; W17's separate realification/fixed-flow
package now supplies it for commutative complex Lie groups. Analytic inverse
and scheme-point dictionary obligations remain separate.

## Verification

Lean 4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Original author commit `f7b456512481d98d9b75ad36713b2167d47b827c`, source base
`2dc949d688c407e32823c4e751679d66b2f40e65` (tree identical to original main).
Named author build: 9,049 jobs, success. All 18 checked declarations report
exactly `[propext, Classical.choice, Quot.sound]`. Only new Contrib files belong
to this PR; historical research notes and scratch logs are banked separately.
The PR includes fresh build/discharge and independent rebuilt-commit evidence.

Existing primitives reused: `Submodule.exists_le_ker_of_lt_top`, finite-dimensional
linear-map continuity, quotient lifting/topology, noncompactness of `ℝ`,
continuous-open homeomorphism construction, and discrete subgroup topology.
A finite source audit did not locate the reverse compact-quotient implication
in the pinned ZLattice/quotient and repository analytic scopes; this is not an
exhaustive whole-library absence claim. No statement or existing module changes,
new dependency, `OneProof.Main` import, `sorry`, new axiom, or build-time code.
