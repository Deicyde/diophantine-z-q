none until the Neron extension of the parametrization lands

# RC pinned generic comparison

Scoped stop. The actual regular Vélu coordinate on the rational quotient is the fixed Laurent generator and evaluates to `j(Nτ)` on every normalized analytic branch, including coordinate collisions. The marked-cover reduction states exactly what is needed for this evaluation to compute the quotient of every pinned pair. The genuine period-lattice pair, the iterated Vélu point map with its exact kernel, and the complementary modular equation all compile. The fixed `rationalAtkin hQ` sends the full analytic chart point to its matrix translate, with coordinates `j(Qτ)` and `j((N/Q)τ)`.

All six new modules passed serialized Lake builds and all 23 axiom checks use only `propext`, `Classical.choice`, and `Quot.sound`. `AtkinCoordinates` used Lake’s unchanged-module mode with the dependency cache from the exact base revision. See the [report](../docs/research/rc-model-generic3.md) for declarations, manuscript verdicts, and references.

`GenericFibreComparison` remains uninstantiated. The remaining steps are marked quotient specialization and identification of the actual pair at every complex normalized point, the equality of the `rationalAtkin` action with `(E/C_Q, (E[Q] + C)/C_Q)`, and the fixed good-Hecke multiset. The source of the latter is the good double coset on the fixed level. Its endpoints are indexed by the p + 1 order-p kernels, including repeated endpoints.

Proposed LEAF for review if needed. For `2 ≤ N` and every `x : RationalCurveComplexPoints (branchFiniteOverQ N)`, there is a τ with `x.left ≫ (X0Model3.finiteChart N).ι = X0Model.complexPoint N τ`, whose complex moduli class is `analyticCyclicPair τ`. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, 1971, Prop. 6.9 and Thm. 6.23 UNVERIFIED. The identification of the printed curve with this normalization also needs checking.

The Néron task uses the restricted fixed parametrization to supply `GoodRow.πInt` for the pinned source. Detector specialization must supply `GoodRow.extension`, `GoodRow.point_W`, and the pointwise Hecke data for `Relations.hecke` and `Relations.eigen`. The report records the exact main locations.

Verified code and report commit `3e1b7f2031cc8826149bbb29b7dc3a5181f2ae9f`. The final handoff SHA is resolved by `git log -1 --format=%H -- .fleet/rc-model-generic3.md`.
