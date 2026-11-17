# semistab-assembly results log

## 11-17 04:30 setup
- Base 8914890c1. Statements read (VERIFIED, read in tree):
  - `ZInQ.HeightFix.IsSemistableRes` PrintedStableHeight.lean:578; `isSemistable_of_res` :590.
  - `ZInQ.R3Residual.IsAnStableHeight` AnalyticStableHeight.lean:710 (clause `IsSemistableRes 𝒩`),
    `BostLowerBoundAn` :856, `GaudronRemondThm14An` :864.
  - `ZInQ.SemiAbDescend.isClosed_range_openSubgroup` SemiAbelianDescendsPerfect.lean:411 (IsAlgClosed).
- Finding (VERIFIED by reading): `HasSemiAbelianIdentityComponent` / `HasSemiAbelianIdCompTorus` assert an
  open *connected* subgroup U, not that U is G⁰; the print says G⁰. The gap is "U clopen".
- Plan: new file ZInQKernel/Contrib/OneProof/SemistablePrintedReadings.lean (namespace ZInQ.SemistabAssembly).
  Closedness over any field: base change to k̄; projection integral (Mathlib IsIntegralHom.SpecMap_iff,
  IsIntegralHom ⇒ UniversallyClosed) and surjective, so U = p(p⁻¹U) closed. (Uses closedness of p rather
  than openness: simpler, same conclusion.)
- Build of AnalyticStableHeight + SemiAbelianDescendsPerfect started (not built in worktree).

## 11-17 04:24 compile
- `lake env lean ZInQKernel/Contrib/OneProof/SemistablePrintedReadings.lean`: VERIFIED compiles, no errors,
  no warnings (after adding `open ZInQ.DefFaltings ZInQ.HeightGlue ZInQ.HeightDict`).
- Proved (VERIFIED, compiled): `isClosed_range_openSubgroup_field` (any field), `range_eq_connectedComponent`,
  `hasSemiAbelianG0_of`, `hasSemiAbelianG0Torus_of`, `isSemistableGeomPrinted_of_res` (reading 1, one lemma),
  `isSemistableResPrinted_of_res` (reading 2), `isSemistablePrinted_of_res`, `isAnStableHeightSS_of`,
  `bostLowerBoundAn_of_ss`, `gaudronRemondThm14An_of_ss`.
- autofold spec scratch/semistab-assembly/autofold.json (count-neutral: GLUE consequence -> GLUE consequence).

## 11-17 04:57 checks
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.SemistablePrintedReadings`:
  VERIFIED "Build completed successfully (16094 jobs)", 0 errors.
- `#discharges` (scratch/semistab-assembly/Discharges.lean, output discharges-output.txt): VERIFIED
  `DISCHARGES [OpenResearchLeaves45.bostLowerBoundAn] by ZInQ.SemistabAssembly.bostLowerBoundAn_of_ss`
  (still assumes BostLowerBoundAnSS) and `[OpenResearchLeaves45.gaudronRemondThm14An] by
  ZInQ.SemistabAssembly.gaudronRemondThm14An_of_ss` (still assumes GaudronRemondThm14AnSS); axioms standard.
- `#print axioms` of the closedness lemma and both bridges: [propext, Classical.choice, Quot.sound].
- `autofold.py scratch/semistab-assembly/autofold.json --dry-run`: VERIFIED exit 0,
  "strict count: 5/29 on 34 -> 5/29 on 34; strictest 5/29 -> 5/29" (count-neutral). flag_class set to
  `pending-review,unverified-locator` (the render_open vocabulary).
