# h21-combine log

Base wip/leaf-fold33b 1a3bab4a (Main: frozenTarget binder `h21S : H21CSteps.TYZThm21Span`). render_open count at base:
39 open (H 10/24 on 34; others h21S, hCM, h33c, hGZss GLUE, hBFH LEAF), per scratch/leaf-fold33/log.md step 37.

1. Merges (no conflicts): origin/wip/h21-gchar d0c2fb93, origin/wip/h21-lcal 8526767e. Hygiene: every scratch .lean
   of both tasks renamed .lean.txt (GChar, FoldCheck, Discharges; H21Lcal, RootPlus, FoldCheck, src/part1-3, fold;
   they copy the declarations now in Contrib, and the FoldChecks name the older frozenTarget signature
   OpenResearchLeaves42); scratch/h21-lcal/src/build.sh paths updated to .lean.txt. No host paths; no vendored code.
2. Modules: scratch/h21-gchar/GChar.lean -> ZInQKernel/Contrib/OneProof/TYZThm21GChar.lean, scratch/h21-lcal/H21Lcal.lean
   -> ZInQKernel/Contrib/OneProof/H21Lcal.lean (unchanged except one header line each). New
   ZInQKernel/Contrib/OneProof/TYZThm21GP.lean: `H21Combine.TYZThm21SpanGP` (h21GP), `tyzThm21Span_of_GP`,
   `tyzThm21SpanGP_of_span`, `tyzThm21SpanGP_iff_span`, `tyzThm21SpanGP_iff_printed`, `tyzThm21PairsC_of_GP`,
   `exists_isLcalSignPrinted` (non-vacuity of the sign premise).
