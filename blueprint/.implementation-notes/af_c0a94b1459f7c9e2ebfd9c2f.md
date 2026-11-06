# The change of variables to C (coordinate-change)

- Lean names: `ZInQ.curveC := Descent.curveB (-delta^2)`, `ZInQ.theta :
  genCurve.toAffine.Point ≃+ curveC.toAffine.Point`, `ZInQ.theta_twoTorsion`, `ZInQ.kummer_theta`.
- Mathlib: `WeierstrassCurve.VariableChange` exists (`Mathlib/AlgebraicGeometry/EllipticCurve/
  VariableChange.lean`) for curves, but v4.35.0 has no induced map on `Affine.Point`; build the
  `AddEquiv` by hand: the map on coordinates plus additivity via `Point.add_some` and slope
  scaling by ε². (If a `Point.map` for variable changes appears upstream, use it.)
- Upstream reuse: `ZInQ.ModelCoordinates.epsilon_inverse`, `delta_identity`, `coordinate_change`
  (lean/ZInQ/ModelCoordinateIdentities.lean), instantiated at `K := K0`, `s := sqrt2`.
- FINITE COMPUTATION: no (symbolic identities, already proved upstream by `linear_combination`).
- Difficulty: medium.
