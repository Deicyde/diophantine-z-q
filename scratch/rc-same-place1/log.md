# rc-same-place1 results log

Base 8b140cd2a. Setup checks: CharFreeSeamTwo.lean, GoodRowWire/SamePlace.lean, rc-hcm-v21g.md exist; `structure OperatorComparison` present. OK.

## Item 1 (doc fixes)
- docs/research/rc-goodrow-wire.md: point/point_W/point_frob/frobenius_sq rows, SamePlaceData owner text, sp row, X row, point_W type row rewritten (owners per generic7 item 1(n)).
- .fleet/rc-goodrow-wire.md: owner paragraph, sp bullet, X bullet.
- docs/research/rc-hcm-v21g.md: only the JetchevKane.classes row.

## Session 2 (resumed after item 1)
- Dependency build (one lake process): CharFreeSeamTwo, PMAdelic.Comparison, GoodRowWire.SamePlace, ModelTarget.Read, Y0LevelPoints. RC was not built in this worktree; Mathlib/vendored oleans present.
- Files drafted under ZInQKernel/Contrib/OneProof/RC/SamePlace/: Supersingular, PointForm, FrobeniusTwist, AtkinLehner, FrobeniusSquare.
- Design: IsSupersingular takes `ell` explicitly (`IsSupersingular ell E`, `ssPoint K ell N`), not `ringChar K`; same predicate for K of characteristic ell.
- resAlgebra ell K := (ModelTarget.resRing ell K).toAlgebra (abbrev, local instance) is the LocalIntegers ell-structure.
- φ lemma hypothesis on f.left stated as `letI := ModelGeneric5.levelCommRing h₅ htame h₂; f.left = Spec.map (ofHom φ)`.
- 6(d) proved by order arithmetic (Q•P, ell•P, gcd(Q,ell)=1) instead of CRT decomposition; same content.
