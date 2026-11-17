/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

NEW EDITION (lane4 , 2026-11-17; G6 fix, lead 2026-11-17T06:11Z). The FLTA name
`ZInQ.Contrib.CloudR2NOS.ClosedSection.FLTA.AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite` is now an `alias` of the lane4-port constant `ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite`, proved in the
route-(E) NEW edition `ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite` (documented lane4
port transform with the published W03 / lane4 dual shims; upstream FLT@6e837e75
`Theorems/Thm_AlgebraicGeometry_Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite.lean` + `P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite.lean`, Apache-2.0, attribution in those files).
SUPERSEDES the macro-expanded adaptation c0f93f15… (review-frozen/closed-section-batch8-audit/), whose
`p2m_open "X"` → plain `open X` expansion did not reopen Mathlib's root `X` under a same-named nested
namespace (latent name-resolution defect); that edition stays frozen as history. Same constant name and
type for every consumer (QuasiFiniteFibre, C3 Step2B3/FieldDescent). SOURCE ONLY, UNCOMPILED.
Options: none. Imports: the previous FLTA link of the original chain (kept so transitive availability is
unchanged) and the canonical Source Thm module.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.FLTA.DescendsLQF
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite

alias ZInQ.Contrib.CloudR2NOS.ClosedSection.FLTA.AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite := ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite
