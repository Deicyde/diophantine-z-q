# unif-printed results log

Target: `BPAnalytic.Uniformization.UniformizationLeafAll` (ZInQKernel/HDecomp/Analytic/Uniformization.lean:91),
bundle field `uniformizationLeafAll` (OpenTextbookLeaves11).

## Stage 1 (scratch/unif-printed/Stage1.lean) — VERIFIED (compiled, `lake env lean`, no errors, no sorry)
- `UnifPrinted.MumfordComplexTorus` : Prop — Mumford §1 printed form over Mathlib `IsManifold 𝓘(ℂ,ℂ^g) ω`,
  `LieGroup 𝓘(ℂ,ℂ^g) ω`, T2, compact, connected ⇒ ∃ lattice Λ and biholomorphic additive-to-multiplicative
  `Torus Λ ≃ₘ^ω X`.
- `UnifPrinted.IsAnalyticStr A g` : the 4 clauses (U(ℂ) open; regular functions ContMDiffOn ω on U(ℂ); g regular
  functions are a local diffeomorphism at each point; topology = topology of regular functions).
- `UnifPrinted.AbVarAnalyticLieGroup` (composite, intermediate).
- `isLocalDiffeomorphAt_proj` (proved): proj : E → E⧸Λ is a local biholomorphism.
- `uniformizationLeafAll_of_lieGroup : MumfordComplexTorus → AbVarAnalyticLieGroup → UniformizationLeafAll` (proved).
