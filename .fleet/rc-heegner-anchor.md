# The genuine Heegner anchor

`HeegnerAnchor.cmPointsAtScale` proves the CM comparison on the actual
`X0Branch.model N`: one rational morphism works at every admissible
conductor. For the form of discriminant `D_K d²` it gives a point over
the ring class field, identifies its complex chart at the Heegner root,
and computes its elliptic image as `phiAn E p.f p.Lat p.κ` under the
fixed embedding. `HeegnerAnchor.genuineHeegnerAnchor` packages those
images and their fields in the anchor of `CCLGenuine`.

The remaining inputs are `CMFieldOfDefinition (X0Branch.model N)`,
the rational representative of the fixed `κ`, and the existing
curve and split imaginary quadratic field data. The norm relations
stay with `CCLThm2_15Applied`; the anchor does not certify compatible
orientations, a common tower identification, or the prepared selectors'
pinned points.

All three Lean files compile with `lake env lean -j1 -DautoImplicit=false`.
All eight theorem axiom checks report only `propext`, `Classical.choice`,
and `Quot.sound`. An initial dependency build briefly overlapped its
replacement, violating the one-process limit. Both were stopped before
the serial checks resumed under a build lock.

The inherited citation issue at tex 1784 and 1788 is recorded in the
report: the cited pair does not supply the normalized newform or Hecke
identity. The proof uses the proved interior parametrization and does
not need the Hecke identity.

Report: `docs/research/rc-heegner-anchor.md`.
Results: `scratch/rc-heegner-anchor/log.md`.

Final implementation and report SHA: `706cf30eb7cc0cafd45c856a6620fabf8ca3b8b7`.
The final branch SHA is returned by
`git log -1 --format=%H -- .fleet/rc-heegner-anchor.md`;
a commit cannot contain its own SHA.

Update: `CCLThm2_15Applied` and `CCLGenuine` are retired; the staged path uses
`CCLThm2_15AppliedWithUnits`. See docs/research/ccl-retire.md.
