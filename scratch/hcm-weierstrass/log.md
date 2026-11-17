# hcm-weierstrass results log

Task: remove step G1 of hCM (ShimuraThm54): prove the Weierstrass map ℂ/Λ → E(ℂ) is biholomorphic for an
intrinsic complex structure on E(ℂ) = WeierstrassCurve.Affine.Point, and IsAnalyticUnif ↔ analytic isomorphism.

## Plan (2026-11-17 02:30)
- Topology on W.toAffine.Point: transported from OnePoint {p : ℂ×ℂ // W.Nonsingular p.1 p.2} (one-point
  compactification of the affine curve = subspace topology of P²(ℂ) for a smooth cubic).
- Charts: x away from y=0, y at 2-torsion, t = -x/y at O; sources ξ(S) with S open in ℂ.
- Abstract machinery: ξ continuous, open, ξ z = ξ w ↔ z-w ∈ Λ, chart data ⇒ ChartedSpace + IsManifold 𝓘(ℂ) ω
  + IsLocalDiffeomorph ξ.
