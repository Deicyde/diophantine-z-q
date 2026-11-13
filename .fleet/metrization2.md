# metrization2 (fleet summary)

**Verdict.**
- `JacDetNondegenerate` (glue) is **proved** from one smaller, analysis-free glue Prop,
  `ZInQ.Metrization2.ProductMapLocalStructure`. That Prop is the local structure, at complex
  points, of any morphism `𝒢₁ ×_{𝓞_L} 𝒢₂ → ℋ`.
- The same Prop implies metrization's open glue `ProductLocalStructure`, so two open glue Props
  become one.
- The leaf `AnalyticUniformizationOfDim` is **proved from T35 `UniformizationExists`**, which is
  already `TextbookLeaves.t35`. So it is no longer a leaf.

**Proof idea.** Suppose all Jacobians vanish. Then some direction `v` is killed by `d(b∘Φ)(0)`
for every regular `b` near the origin (linear algebra; subtract `b`'s pull-back from the unit
section). Translation through the group law extends this to every point. So every regular
function is constant along `t ↦ Φ(tv)` on an affine chart. Since points of an affine scheme are
determined by their values, `Φ(tv) = 1`, which contradicts the discreteness of `Λ`. The proof
uses neither the complex-manifold structure of `A(ℂ)` nor `dim A = g`.

**T35 ⇒ `AnalyticUniformizationOfDim`.** Apply T35 to `A_L` at `τ` (`dim A_L = dim A` by g0-dim)
and transport along the group isomorphism `A_L(ℂ)_τ ≅ 𝒢(ℂ)_τ`. That isomorphism is built from the
monoidal functor `Over.pullback (Spec L → Spec 𝓞_L)`.

**bp-analytic's `UniformizationLeaf`.** It is neither weaker nor stronger as it stands: `g` is not
pinned, its clauses are stronger, and it is stated only over `ℂ`. It is not in the bundles, so T35
is the one uniformization leaf.

**What compiles.** `scratch/metrization2/Metrization2.lean`, built by `build.sh`, imports only
Mathlib: 0 errors, no sorry or axiom, standard axioms only. It contains `jacDetNondegenerate_of`,
`productLocalStructure_of`, `analyticUniformizationOfDim_of_uniformizationExists` and
`HSyn.G0Split.heightAdditivity_of_metrization_v4`. The `_v4` theorem takes N1, H5,
`AnalyticUniformizationUnique`, `HodgeLatticeTheorem`, T35, `ProductMapLocalStructure` and
`ProductHodgeLattice`.

**What remains.**
- `ProductMapLocalStructure` (glue): affine opens of a fibre product as `Spec(R₁ ⊗ R₂)`, a basic
  open and a fraction `a/h^N`. It is pure Mathlib scheme theory and not yet proved.
- `ProductHodgeLattice`, plus `AnalyticUniformizationUnique` and `HodgeLatticeTheorem` from
  def-faltings, are unchanged.

Report: docs/research/metrization2.md; log: scratch/metrization2/log.md.
