# CloudB3W17LocalExp — from a local or global analytic homomorphism to the complex torus

Four files, all **new**, no existing module changed. Lean 4.35.0, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, base `2dc949d68` (restored main). Every declaration has
axioms `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `axiom`, no `#eval`/`run_cmd`/
`initialize`/`syntax`/`notation`/macro/elaborator.

| file | content |
| --- | --- |
| `Globalization.lean` | a *local* analytic homomorphism `L` on `ball 0 r` extends to a global one (`glob r L v = L (v/n)^n`), uniquely; analyticity, openness, surjectivity, discrete full-lattice kernel, `Torus Λ ≃ₘ^ω G` |
| `GlobalHom.lean` | the same conclusion for a **given global** homomorphism with `LocalInverseData` (an analytic local section at `1` plus injectivity near `0`), with the kernel named: `torus_diffeo_of_globalHom` |
| `ManifoldIFT.lean` | the **analytic inverse function theorem with vector-space source and manifold target**, missing from Mathlib |
| `UnconditionalTorus.lean` | the unconditional theorem: a compact connected commutative complex Lie group is a complex torus |

## The inverse function theorem (new, general)

```lean
theorem CloudB3W17LocalExp.isLocalDiffeomorphAt_of_hasMFDerivAt
    {𝕜 : Type*} [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {M : Type*} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(𝕜, F) ω M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [CompleteSpace F]
    {f : E → M} {a : E} {e : E ≃L[𝕜] F}
    (hf : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) ω f a)
    (hd : HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, F) f a (e : E →L[𝕜] F)) :
    IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, F) ω f a
```

Mathlib has the normed-space inverse function theorem (`ContDiffAt.toOpenPartialHomeomorph`,
`ContDiffAt.to_localInverse`) and the forward manifold direction
(`IsLocalDiffeomorphAt.isInvertible_mfderiv`), but not this converse. Proof: in the chart `c` at
`f a`, `ψ = c ∘ f` is analytic at `a` and `mfderiv c (f a) ∘ e` is invertible (a chart of an analytic
manifold is a `PartialDiffeomorph`, `chartPartialDiffeo`); Mathlib's theorem gives a partial
homeomorphism at `a` with analytic inverse at `ψ a`; restricting its `PartialEquiv` to the open set
where `ψ` is analytic, its inverse is analytic, and `f` lands in the chart turns it into a
`PartialDiffeomorph`, and composing with the chart's inverse gives one for `f`. Stated for any
`RCLike` field, so it serves the real case too.

## The unconditional theorem

```lean
theorem CloudB3W17LocalExp.exists_torus_diffeo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [CommGroup G] [LieGroup 𝓘(ℂ, E) ω G]
    [CompactSpace G] [ConnectedSpace G] :
    ∃ (Λ : Submodule ℤ E) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
      (e : BPAnalytic.Torus Λ ≃ₘ^ω⟮𝓘(ℂ, E), 𝓘(ℂ, E)⟯ G), ∀ a b, e (a + b) = e a * e b
```

`exists_exp_torus_diffeo` is the full form (the exponential itself, its surjectivity, the kernel
description `v ∈ Λ ↔ exp v = 1`, and `e (proj Λ v) = exp v`), and

```lean
theorem CloudB3W17LocalExp.mumfordComplexTorus_comm (g : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (Fin g → ℂ) X] [CommGroup X]
    (hman : IsManifold 𝓘(ℂ, Fin g → ℂ) ω X) (hlie : LieGroup 𝓘(ℂ, Fin g → ℂ) ω X)
    (hcpt : CompactSpace X) (hconn : ConnectedSpace X) :
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
      (e : BPAnalytic.Torus Λ ≃ₘ^ω⟮𝓘(ℂ, Fin g → ℂ), 𝓘(ℂ, Fin g → ℂ)⟯ X), ∀ a b, e (a + b) = e a * e b
```

is the conclusion of the H103 printed leaf `UnifPrinted.MumfordComplexTorus` in the commutative case,
with `T2Space` dropped (not needed). It is **not** a discharge of that leaf: the leaf quantifies over
all `Group` structures, and commutativity of a general compact connected complex Lie group is not
proved here. For abelian varieties it is not needed — `A.Pt ℂ` is commutative
(`ZInQKernel/HDecomp/Objects.lean:177`).

## Inputs

* the exponential: `CloudB3W17Realify.exists_complexExp` (realifier branch
  `cloud-b3/w17-complex-exp` at `066ffb3e5`, merged here read-only) — a global analytic homomorphism
  with identity derivative at `0`, built from complexified real flows, assuming no compactness or
  connectedness;
* the lattice: `CloudB3W17Lattice.isZLattice_of_exp` (branch `cloud-b3/w17-lattice-compact`), which
  rests on `isZLattice_of_compactSpace_quotient` (discrete + compact quotient ⇒ full lattice, also
  missing from Mathlib);
* the torus's analytic structure: `BPAnalytic.Torus` (`ZInQKernel/HDecomp/Analytic/Torus.lean`),
  not re-proved here.

## Not done

* No in-tree instance of the hypotheses is exhibited (the natural witness,
  `Multiplicative (BPAnalytic.Torus Λ)`, needs `ChartedSpace`/`LieGroup` instances transported along
  the `Multiplicative` type synonym, which Mathlib does not provide).
* Commutativity of a general compact connected complex Lie group (Mumford §1's first half).
