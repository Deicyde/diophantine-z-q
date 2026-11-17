/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

NEW EDITION (lane4 a940f2af, 2026-11-17; G6 fix, lead 2026-11-17T06:11Z). The FLTA name
`ZInQ.Contrib.CloudR2NOS.ClosedSection.FLTA.RingHom.QuasiFinite.codescendsAlong_faithfullyFlat` is now an `alias` of the lane4-port constant `ZInQ.Contrib.CloudW03NeronSurj.FLT.RingHom.QuasiFinite.codescendsAlong_faithfullyFlat`, proved in the
route-(E) NEW edition `ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat` (documented lane4
port transform with the published W03 / lane4 dual shims; upstream FLT@6e837e75
`Theorems/Thm_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat.lean` + `P2M/Sol/S_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat.lean`, Apache-2.0, attribution in those files).
SUPERSEDES the macro-expanded adaptation a6c3f894… (review-frozen/closed-section-batch8-audit/), whose
`p2m_open "X"` → plain `open X` expansion did not reopen Mathlib's root `X` under a same-named nested
namespace (latent name-resolution defect); that edition stays frozen as history. Same constant name and
type for every consumer (QuasiFiniteFibre, C3 Step2B3/FieldDescent). SOURCE ONLY, UNCOMPILED.
Options: none. Imports: the previous FLTA link of the original chain (kept so transitive availability is
unchanged) and the canonical Source Thm module.
-/
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat

alias ZInQ.Contrib.CloudR2NOS.ClosedSection.FLTA.RingHom.QuasiFinite.codescendsAlong_faithfullyFlat := ZInQ.Contrib.CloudW03NeronSurj.FLT.RingHom.QuasiFinite.codescendsAlong_faithfullyFlat
