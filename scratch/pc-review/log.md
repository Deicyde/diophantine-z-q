# pc-review results log

## Step 1: build (merged tree 807515d42)
- First build of PoleCompletenessFromRCCore2 + PoleCompletenessFromRCGenuine FAILED (merge breakage, two causes):
  - F1 `ZInQKernel/Contrib/PoleRC/Rescale.lean:46` (round 1 file): `simp only [polePoly]` no longer unfolds the body,
    because fork main (379379da7, lane74 #76) turned `Manuscript.polePoly`/`PoleSoluble`/`PoleCompleteness` into
    abbrevs of the `ZInQ` ones. FIX: `simp only [polePoly, ZInQ.polePoly]`. VERIFIED (compiles).
  - F2 `ZInQKernel/Contrib/PoleRC/MordellWeilM.lean:2` (cloud file) imports `ZInQKernel.RouteK.RankMW.Image`, which
    fork main deleted with Route K (c575ab5ec). FIX: verbatim copy of that file at f13d7a5ad as
    `ZInQKernel/Contrib/PoleRC/MWImage.lean` (same namespace `ZInQ.RouteK.Rank`, header note added), import redirected.
- After F1, F2: `lake build ...Core2 ...Genuine` -> Build completed successfully (9502 jobs). VERIFIED.
