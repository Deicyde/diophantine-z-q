# rv-fast results log

Base: wip/rv-fast b7cdba8e + merges of origin/wip/{curve-infra 0eb4618a (already in base), lg-kerwild 745af133 (already in base), unram-roots b066d686, afr-absfrob 2ffcf322}.

## Reproducibility of assembled files (VERIFIED, 10:25)
Re-ran each task's assembly script with output to /tmp/rvf and `cmp` against the committed file:
- curve-infra/CurveInfraAll.lean (mk_all.sh): identical.
- unram-roots/UnramRoots.lean (build.sh): identical.
- afr-absfrob/AfrAbsFrob.lean (build.sh): identical.
- lg-kerwild/KerWild.lean (build.sh): DIFFERS. scratch/local-glue/LocalGlue.lean changed after lg-kerwild built
  (local-glue commits b582bf03, d2f6d6d1: added a verbatim g0-dim DimBlock, `localGlue_of_baseChange'`, and dropped
  `A₀.dim = 2` from `G7LocalPackBC`). The defs KerWild, DescentPts, LocalGlue, G7Clauses, UnramRoots are not in the
  diff (unchanged). The committed KerWild.lean is the file that was compiled; rebuilding it today would duplicate
  the G0Dim block (lg-kerwild also splices g0-dim's Dim.lean) -> integration conflict, not a soundness issue.
