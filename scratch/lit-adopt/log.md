# lit-adopt log

## Step 1: ZInQKernel/Hypotheses/CR3Literature.lean
- From scratch/wk-cr3/Literature.lean, namespace ZInQ.Literature; #print axioms lines and
  frozenTarget_of_sixContactMin_literature dropped (main theorem moves to MainLiterature.lean).
- (a) FunctionalEquation5 restricted to 0 < s.re < 2; docstring explains the Gamma junk value
  at 0, -1, ...; rootNumberVanishing_of_functionalEquation passes `by norm_num` twice at s = 1.
- (b) GrossZagierKolyvagin renamed GrossZagier; supplier for L(E^K,1) ≠ 0 is BFH 1990 (via
  Waldspurger) or Friedberg-Hoffstein 1995; Murty-Murty removed; Kolyvagin remark kept.
- (c) module docstring with a Trust section (one item per Prop, L-series, IsLContinuation.eq).
- Deviation: import ZInQKernel.RouteK.RankVariants dropped (only the main theorem used it).
- Deviation: IsLContinuation.eq's last step split into two `have`s (100-char line limit).
- `lake build ZInQKernel.Hypotheses.CR3Literature`: success (only "module system" import
  warnings from Mathlib's per-module imports).
