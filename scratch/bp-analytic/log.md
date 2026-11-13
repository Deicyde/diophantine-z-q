# bp-analytic results log

## 2026-11-12

- Torus.lean §1 (charts, manifold): `exists_gap`, `eventuallyEq_add_const`, `contDiffOn_of_sub_mem`,
  `Torus`, `proj`, `proj_eq_iff`, `isAddQuotientCoveringMap_proj`, `isCoveringMap_proj`,
  `isLocalHomeomorph_proj`, `chartOf` (+ API), `ChartedSpace E (Torus Λ)`, `transition_sub_mem`,
  `IsManifold 𝓘(ℂ, E) ω (Torus Λ)`. COMPILED (lake env lean, 1m13s, warnings only).
- Mathlib facts used (VERIFIED by reading .lake/packages/mathlib): `AddSubgroup.isAddQuotientCoveringMap_of_comm`
  (Topology/Covering/Quotient.lean), `IsLocalHomeomorph.localInverseAt` (Topology/IsLocalHomeomorph.lean),
  `isManifold_of_contDiffOn` (Geometry/Manifold/IsManifold/Basic.lean). Mathlib's
  `Geometry/Manifold/Instances/Quotient.lean` gives only a `ChartedSpace` on `orbitRel.Quotient`; its TODO
  is exactly the `IsManifold` instance built here.
- Torus.lean §2-3: `contMDiff_proj` (proj analytic), `contMDiff_of_comp_proj`, `contMDiff_of_comp_proj₂`
  (descent of C^n maps along proj), `lieAddGroup_torus : LieAddGroup 𝓘(ℂ, E) ω (Torus Λ)`,
  `connectedSpace_torus`, `compactSpace_torus` (full lattice), `AddGroupLieAlgebra 𝓘(ℂ,E) (Torus Λ) = E` (rfl),
  `torusExp : E →+ Torus Λ`, `torusExp_surjective`, `ker_torusExp : ker = Λ`, `contMDiff_torusExp`,
  `contMDiff_torusExp_smul` (one-parameter subgroups analytic), `holomorphic_const` (Liouville on the torus,
  from Mathlib `MDifferentiable.exists_eq_const_of_compactSpace`). COMPILED, no errors/warnings;
  `#print axioms` on isManifold_torus, lieAddGroup_torus, compactSpace_torus, holomorphic_const, ker_torusExp,
  contMDiff_torusExp_smul: [propext, Classical.choice, Quot.sound].
