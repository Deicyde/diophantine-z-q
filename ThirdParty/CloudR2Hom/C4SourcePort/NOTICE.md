# C4SourcePort — Attribution and Modification Notice

## Port contributions

Copyright (c) 2026 H70 source-port contributors.

The original C4SourcePort contributions are released under the Apache License,
Version 2.0. See `LICENSE` in this directory.

## Mathematical source and supplier attribution

`ProjectiveEmbedding.lean` uses the general projective-immersion theorem from:

- Repository: <https://github.com/frenzymath/Jacobian-Challenge>
- Commit: `c4254cce15b3e284a0a3ae1d73936f2ee195d272`
- Module: `Jacobian.AlgebraicGeometry.Group.QuasiProjective`
- Theorem: `GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral`

Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu.

The supplier is distributed under the Apache License, Version 2.0. The existing
published supplier in `ZInQKernel/Contrib/CloudW07JacobiansCurves/` is reused
without further modification. Its own `LICENSE`, `NOTICE`, file-level credits,
and published modification notices remain there unchanged. This notice does not
replace or alter those supplier notices.

## Modifications and original work

- `ProjectiveEmbedding.lean` is a new thin application of the supplied theorem
  to the original `PkgI3.AbVar` scheme. It upgrades the supplied projective
  immersion to a closed immersion using that object's properness. The source
  scheme and its structure morphism are preserved; no second copy or alteration
  of the supplier proof is introduced.
- `ClosedImmersion.lean` is original work over Mathlib commit
  `56a005855ea17e0b0958f73ec801ae140b0a1679`. It proves the closed-immersion upgrade
  using the existing properness, universal-closedness, and preimmersion APIs.
  Mathlib retains its own Apache-2.0 licensing and author attributions.

This publication notice records the provenance and changes of these two files;
it does not modify either Lean source file or relicense any dependency.
