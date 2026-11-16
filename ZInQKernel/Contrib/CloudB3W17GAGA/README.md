# W17: analytic quotient descent and supplied-target graphs

Import `ZInQKernel.Contrib.CloudB3W17GAGA.Descent` or `.Graph`.

`existsUnique_regular_analytic_descent` proves that an actual
`ZInQ.HomLattice.IsAnalyticHom σ ψ` killing a discrete lattice descends uniquely
as an additive map from the quotient. Every regular-function domain is open;
every regular evaluation is `MDifferentiableOn` on that domain. This works for
arbitrary `K/σ`, with no full-lattice, dimension or uniformization-existence leaf.
It never differentiates junk regular-function values off their domain.

Given a supplied strong target torus, `exists_closed_compact_targetTorusGraph`
proves an exact closed additive graph, compact carrier when the source is
compact, analytic parametrization, and a split complex differential at every
point. The explicit `graphHomeomorph` parametrizes the graph and its inverse is
the ambient first projection. Target compactness is not assumed.
Existing strong-target comparison and complex-linear lifting are reused.

**Neither theorem algebraizes the graph or closes `GAGAMorphism`.** A closed or
compact analytic graph does not itself produce a coherent ideal or an algebraic
morphism. Canonical scheme-analytic identification, coherent-ideal
algebraization, and projection-isomorphism reflection remain explicit work.
The exact original target has no target-torus or source-fullness premises;
they are clearly visible conditions of this optional graph supplier only.

## Verification and provenance

Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Original author head `64726068607df8dfe2cfdba07a71a8c6f1ca3613`, base restored
main `2dc949d688c407e32823c4e751679d66b2f40e65`. Two new Lean modules, 357 lines;
all 27 checked declarations use exactly `propext`, `Classical.choice`, `Quot.sound`.
The author's module and exact-usage checks compiled; an independent fresh build
of `Graph` emits two benign Mathlib module-system import advisories. Author
measurement: four threads, maximum successful RSS 6,952,572 KB. Independent
fresh build: maximum RSS 16,144,640 KB. Fresh named build/discharge and independent
rebuilt-pushed-commit review are separate PR evidence, not inferred from that run.

Reused actual quotient lifting/charts, `continuous_symm_comp_strong`,
`exists_complexLinear_of_analytic_strong`, existing BPAnalytic projection descent,
closed-subgroup topology, and differential immersion APIs. No duplicated scalar
restriction, lattice fullness, or zero-dimensional work. No existing target or
module edits, `OneProof.Main` import, new dependency, new axiom, `sorry`, or
build-time syntax/notation/macro/elaborator code.

Source locator correction (actual SGA 1 recomposed math/0206203v2 read): XII
**Corollary 4.5**, pp. 250–251 (old margin 331–332), is proper-scheme morphism
full faithfulness; Theorem 4.4 is coherent-sheaf equivalence. A future
graph-algebraization proof would also need XII 3.1(ix), isomorphism reflection.
None of these printed SGA 1 results is used by the delivered Descent/Graph
proofs. Both source and target proper is
sufficient for the exact abelian-variety target. No existing target docstring
was modified to correct this citation.
