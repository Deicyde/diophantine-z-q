# CloudB3W17LocalExp — globalizing a local analytic homomorphism

`Globalization.lean` proves a **conditional** theorem. It supplies no exponential map, no analytification,
no commutativity of a general compact complex Lie group, and discharges no open hypothesis of the project.

Base `2dc949d68` (restored main), Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
All 26 declarations have axioms `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `axiom`, no
`#eval`/`run_cmd`/`initialize`/`syntax`/`notation`/macro/elaborator.

## The theorem

```lean
theorem CloudB3W17LocalExp.exists_torus_diffeo_of_localExp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]
    [LieGroup 𝓘(ℂ, E) ω G] [CompactSpace G] [ConnectedSpace G]
    {r : ℝ} {L : E → G}
    (hr : 0 < r) (hL : IsLocalHom r L)
    (hLsm : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω L (Metric.ball 0 r))
    (hLloc : IsLocalDiffeomorphAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω L 0) :
    ∃ (Λ : Submodule ℤ E) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
      (e : BPAnalytic.Torus Λ ≃ₘ^ω⟮𝓘(ℂ, E), 𝓘(ℂ, E)⟯ G), ∀ a b, e (a + b) = e a * e b
```

`IsLocalHom r L` is the two-field structure `L 0 = 1` and `L (x + y) = L x * L y` for `x`, `y`, `x + y` all in
`ball 0 r`. **Nothing is assumed about `L` outside that ball**: `glob r L` is built from the restriction, and
junk values of `L` elsewhere are never used (`glob_eq_of` picks its own denominator).

With `E := Fin g → ℂ` the conclusion is literally the conclusion of `UnifPrinted.MumfordComplexTorus` (the
unif-printed leaf) in the commutative case. What remains open is only its hypothesis: the existence of `L`,
i.e. the exponential map.

## Intermediate results (all proved)

| name | content |
| --- | --- |
| `glob r L v = L (v / n) ^ n` | the globalization, `n = nOf r v` |
| `glob_eq_of` | any admissible denominator computes it (`n`-independence, by the `L (k • w) = L w ^ k` law inside the ball) |
| `glob_eq_self` | `glob = L` on `ball 0 r`; `glob_zero` |
| `glob_add` | `glob` is a homomorphism on all of `E` — commutativity of `G` enters here (`mul_pow`) |
| `glob_unique` | any homomorphism `E → G` agreeing with `L` on the ball equals `glob` |
| `glob_contMDiff` | `glob` is analytic: near `v₀` it is `(L ∘ (· / n)) ^ n` with `n` fixed |
| `sect`, `one_mem_sect`, `glob_sect` | the local analytic section `Ψ⁻¹` of `glob` on an open neighbourhood of `1` |
| `glob_isOpenMap` | open at `1` by the section, everywhere by translation |
| `glob_surjective` | the range is an open, hence closed, subgroup of a connected group |
| `glob_injOn` | `glob` is injective on `Ψ.source ∩ ball 0 r` |

## What the proof reuses

* Lattice half — **not** re-proved here: `CloudB3W17Lattice.isZLattice_of_exp` (discrete kernel, full lattice,
  `Torus Λ ≃ₜ+ Additive G`), which rests on `CloudB3W17Lattice.isZLattice_of_compactSpace_quotient`.
* Torus side — **not** re-proved here: `BPAnalytic.Torus`, `contMDiff_proj`, `contMDiff_of_comp_proj`,
  `isManifold_torus` (`ZInQKernel/HDecomp/Analytic/Torus.lean`).
* Mathlib: `contMDiff_pow`, `contMDiff_mul_left`, `topologicalGroup_of_lieGroup`, `isOpenMap_mul_left`,
  `Subgroup.isOpen_of_mem_nhds`, `Subgroup.isClosed_of_isOpen`, `IsClopen.eq_univ`,
  `ContinuousOn.isOpen_inter_preimage`, `PartialDiffeomorph`, `contMDiff_iff_contDiff`.

The analytic inverse is built by hand from the local section (`F⁻¹ g = proj (v₀ + Ψ⁻¹ (g₀⁻¹ g))` near `g₀`),
so no local-diffeomorphism-of-`proj` lemma is duplicated from the host's unif-printed module (which is not on
`main` and is not imported).

## Hypothesis shape, and the honest blocker

* `IsLocalDiffeomorphAt … L 0` is used rather than "`HasMFDerivAt` with invertible derivative" because Mathlib
  (pin `56a0058`) has no inverse function theorem *for manifolds*: `IsLocalDiffeomorphAt.isInvertible_mfderiv`
  goes one way only. A printed exponential supplies the local-biholomorphism form directly, so this costs
  nothing against the literature while keeping the file free of an unproved IFT step.
* `T2Space G` is **not** needed anywhere.
* The missing input is the local analytic homomorphism itself. Mathlib has no Lie-group exponential, and the
  ODE API cannot produce one: `Mathlib/Analysis/ODE/PicardLindelof.lean` gives Lipschitz — not differentiable —
  dependence on initial conditions, and its `C^n` statements are in time, with the comment
  "TODO: Extend to the analytic `n = ⊤` case". Constructing `L` is therefore out of scope here, and no printed
  `Prop` for it is introduced in this file (that would need an exact source reading first).
