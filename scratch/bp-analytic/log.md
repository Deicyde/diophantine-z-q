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
