# frontier: every open Prop on the path to `ZInQ.FrozenTarget`

Task frontier, 2026-11-13. DRAFT (being filled in; sections marked TODO are not yet checked).

Marks: **VERIFIED** (read in a named Lean file or report at a named commit, or compiled),
**STANDARD** (published, exact reference), **SPECULATIVE**, **UNVERIFIED** (a locator taken from a
report or from memory; this host has no network).

Classification (the integrator's rule, applied strictly): **LEAF** = a published, refereed statement,
and the Lean Prop is never stronger than the published one. Everything else is **GLUE**, including
statements that are standard but not printed in that form, composites of several published theorems
("literature composite") and consequences of a printed theorem.

## GZ: `ZInQ.Literature.GrossZagier`

Chain (VERIFIED, read in the Lean files):
- `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner :
  SixContactMin → Literature.TYZThm35ReadingA → GZDecomp.FHNonvanishing → GZDecomp.GrossZagierHeegner →
  FrozenTarget` (ZInQKernel/Contrib/GZTheta/NewCMFinal.lean, branch wip/atkin-li 6f77abb1), from
  `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` (Contrib/GZDecomp/Decomp.lean,
  fork main) and atkin-li's `ZInQ.GZTheta.heckeThetaNewform : GZDecomp.HeckeThetaNewform`.

Open: `ZInQ.GZDecomp.FHNonvanishing`, `ZInQ.GZDecomp.GrossZagierHeegner` (both GLUE in the strict
sense: literature composites; TODO details).
