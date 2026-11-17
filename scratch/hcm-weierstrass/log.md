# hcm-weierstrass results log

Task: remove step G1 of hCM (ShimuraThm54): prove the Weierstrass map ℂ/Λ → E(ℂ) is biholomorphic for an
intrinsic complex structure on E(ℂ) = WeierstrassCurve.Affine.Point, and IsAnalyticUnif ↔ analytic isomorphism.

## Plan (2026-11-17 02:30)
- Topology on W.toAffine.Point: transported from OnePoint {p : ℂ×ℂ // W.Nonsingular p.1 p.2} (one-point
  compactification of the affine curve = subspace topology of P²(ℂ) for a smooth cubic).
- Charts: x away from y=0, y at 2-torsion, t = -x/y at O; sources ξ(S) with S open in ℂ.
- Abstract machinery: ξ continuous, open, ξ z = ξ w ↔ z-w ∈ Λ, chart data ⇒ ChartedSpace + IsManifold 𝓘(ℂ) ω
  + IsLocalDiffeomorph ξ.

## Results (2026-11-17 02:20-03:00), all VERIFIED (compiled, `lake env lean scratch/hcm-weierstrass/W.lean`, then
`lake build ZInQKernel.Contrib.OneProof.ShimuraThm54Biholo`: Build completed successfully)
- Part A (A_Charts.lean): ChartDatum (c : E → ℂ, e : OpenPartialHomeomorph ℂ ℂ, c∘ξ = e on e.source, e' ≠ 0);
  ChartDatum.chart : OpenPartialHomeomorph E ℂ (source ξ(e.source)); chartedSpaceOf; transition_contDiffOn;
  isManifoldOf (IsManifold 𝓘(ℂ) ω); contMDiff_of; isLocalDiffeomorph_of. Hypotheses: ξ continuous, open, fibres =
  Λ-cosets. Compiled first try except two small fixes.
- Part B/C (B_body.lean): pointTopology (induced from OnePoint {p // Nonsingular}); coordinates xC yC tC coordFor;
  eventually_large_weierstrassP; continuous_toPoint; exists_compact_fund; isOpenMap_toPoint;
  deriv_derivWeierstrassP (℘'' = 6℘² − g₂/2 off Λ, via derivative of the differential equation + identity theorem
  on the connected Λᶜ + ℘'(ω₁/4) ≠ 0); exists_chartDatum_zero (t∘ξ = 2(z+z³E)/(2−z³D) near 0, derivative 1);
  exists_chartDatum_some (x or y); exists_chartDatum_toPoint.
- Part D: UnifProps, exists_unifProps (via exists_lattice_eq), unif (chosen), chartedSpacePoint, atlas_coord,
  chartAt_coe (chart at P has coordinate coordFor P), isManifoldPoint, unif_isLocalDiffeomorph; IsAnalyticIso.
- Part E: isLocalDiffeomorph_comp_mul, exists_eq_unif_mul, isAnalyticIso_of_isAnalyticUnif,
  exists_local_lift_unif, isAnalyticUnif_of_isAnalyticIso (with group law), isAnalyticUnif_iff_isAnalyticIso,
  toPoint_isAnalyticIso.
- Part F: deriv_eq_of_lifts, eq_unif_mul_of_isAnalyticIso (biholomorphism with 0 ↦ O is z ↦ unif(αz): compact
  fundamental set from compactness of E(ℂ), local lifts, Liouville on the lift derivative, clopen argument),
  add_of_isAnalyticIso, isAnalyticUnif_iff_isAnalyticIso_zero.
- Part G: isShortNF_map instance; leaf ShimuraThm54Biholo; shimuraThm54_of_biholo : ShimuraThm54Biholo → ShimuraThm54.
- Axioms (Axioms-output.txt): shimuraThm54_of_biholo, toPoint_isAnalyticIso, both dictionaries,
  add_of_isAnalyticIso, isManifoldPoint, chartAt_coe, atlas_coord: [propext, Classical.choice, Quot.sound].
- Contrib file: ZInQKernel/Contrib/OneProof/ShimuraThm54Biholo.lean (60 KB; namespace
  ZInQ.Contrib.HCMWeierstrass; instances scoped), built in 37 s.
