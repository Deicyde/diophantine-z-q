# RC model levels handoff

The finite étale exact-order cover compiles over the universal short Weierstrass locus. Its field-valued points are precisely points of additive order `N`, with the identity as the level-one point. Lean checks the coprime multiplication formulas, the unit orbits of geometric generators, the short-chart stabilizers, and the explicit type of pair classes. The quotient constructor gives the p-free affine scheme over the detector's local ring, together with flatness and arbitrary scalar extension, given a compatible graded unit action.

The pointwise reduction proof identifies the actual cyclic kernels on the geometric generic and residue fibres at all good primes, including `p ≡ 1 (mod ℓ₀)`. The odd-order Vélu quotient equations specialize, and an Atkin–Lehner kernel generator preserves its order. The quotient isogenies and the transported cyclic level subgroups still require compatibility with reduction.

The next algebra steps are the affine restriction squares for exact-order base change and the lift of the unit action and weight grading to the universal algebra. The coarse point bijection, finite type, smoothness, and Néron extension remain. `GenericFibreComparison` states the open comparison with the fixed generic model and its operator and parametrization readings. The report gives the remaining steps and unverified print locators. [Research report](../docs/research/rc-model-levels.md)

All 16 modules passed Lake with the permitted axioms. The initial build allowed concurrent prerequisite compilers. The subsequent builds and final audit serialized the compiler invocations in the required resource scope.

Verified source and report commit `43668181bc8f0ccf7c146ed2b8b0511aed22f344`. The final handoff commit is identified by `git log -1 --format=%H -- .fleet/rc-model-levels.md`.
