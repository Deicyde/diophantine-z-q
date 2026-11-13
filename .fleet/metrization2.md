# metrization2 (fleet summary)

**Verdict: both targets resolved, with no new leaf and no new open glue.**
- `ZInQ.Metrization.JacDetNondegenerate` (glue) is **proved, with no hypotheses**
  (`ZInQ.Metrization2.jacDetNondegenerate`).
- Metrization's other open glue `ProductLocalStructure` is also **proved**
  (`ZInQ.Metrization2.productLocalStructure`).
- The leaf `AnalyticUniformizationOfDim` is **proved from T35 `UniformizationExists`**, which is
  already `TextbookLeaves.t35`. So it is no longer a leaf.

**How.**
- *`JacDetNondegenerate`.* Suppose all Jacobians vanish. Then some direction `v` is killed by
  `d(b∘Φ)(0)` for every regular `b` near the origin (linear algebra; subtract `b`'s pull-back from
  the unit section). Translation through the group law extends this to every point. That step
  needs the local structure, at complex points, of a morphism out of `𝒢₁ ×_{𝓞_L} 𝒢₂`
  (`ProductMapLocalStructure`). So every regular function is constant along `t ↦ Φ(tv)` on an
  affine chart. Since points of an affine scheme are determined by their values, `Φ(tv) = 1`,
  which contradicts the discreteness of `Λ`. No complex-manifold structure on `A(ℂ)` is needed,
  and `dim A = g` is not used.
- *`ProductMapLocalStructure`.* Proved from Mathlib's scheme API: affine opens `Vᵢ`; then
  `Q = V₁ ×_S V₂` is affine with `Γ(Q)` a pushout (`isPushout_appTop_of_isPullback`); every
  element of a pushout of rings is `Σ inl·inr`; a basic open `D(h)`; `t = a/h^N`.
- *T35 ⇒ `AnalyticUniformizationOfDim`.* Apply T35 to `A_L` at `τ` (`dim A_L = dim A` by g0-dim)
  and transport along the group isomorphism `A_L(ℂ)_τ ≅ 𝒢(ℂ)_τ`. That isomorphism is built from
  the monoidal functor `Over.pullback (Spec L → Spec 𝓞_L)`.

**bp-analytic's `UniformizationLeaf`.** It is neither weaker nor stronger as it stands: `g` is not
pinned, its clauses are stronger, and it is stated only over `ℂ`. It is not in the bundles, so T35
is the one uniformization leaf.

**What compiles.** `scratch/metrization2/Metrization2.lean` (6164 lines, built by `build.sh`)
imports only Mathlib: `lake env lean` gives 0 errors in 45 s, no sorry or axiom, standard axioms
only. It contains `HSyn.G0Split.heightAdditivity_of_metrization_v5`, which takes N1, H5,
`AnalyticUniformizationUnique`, `HodgeLatticeTheorem`, T35 and `ProductHodgeLattice`. Metrization's
`_v3` additionally took `AnalyticUniformizationOfDim`, `JacDetNondegenerate` and
`ProductLocalStructure`. It also contains
`metrizationExists_of_uniformizationExists : HodgeLatticeTheorem → T35 → MetrizationExists`.

**Kernel check.** `scratch/metrization2/Kernel.lean` (built by `build_kernel.sh`) imports
`ZInQKernel.HDecomp.LeafPush2.T` and runs the same proofs against the kernel's `PkgI3.AbVar`,
`GroupModel` and T35: 0 errors, standard axioms.

**What remains.**
- Not compiled: integration into the scratch leaf file `Leaves.lean`, which keeps two AbVar
  copies (one `abVarEquiv` step, noted in the report). The kernel itself has a single copy and
  was checked.
- Unchanged, outside this task: `ProductHodgeLattice` (metrization's glue), and
  `AnalyticUniformizationUnique` and `HodgeLatticeTheorem` from def-faltings.

Report: docs/research/metrization2.md; log: scratch/metrization2/log.md.
