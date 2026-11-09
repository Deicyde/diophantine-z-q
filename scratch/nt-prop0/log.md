# nt-prop0 log

## Step 0 (sources read)
- CR3: ZInQKernel/Hypotheses/CertifiedRank.lean (`ZInQ.CertifiedRank`), system in
  ZInQKernel/RouteK/System/Selmer.lean (`Config.IsSol`, `E1`, `E2`, `D`, `twoAdicRows`),
  configuration of d in RouteK/Assembly/Realize.lean (`natConfig`, `natClass`, `primeCfg`),
  `legBit p a = if IsSquare (a : ZMod p) then 0 else 1` (RouteK/Slots/Symbols.lean:17).
- Prop 0: descent-alt §4.1; referee proof rv-slot-k-descent §1.1-1.5 (place 2 by x = 1/4, all 4
  classes); slot-k §2.1, §4.1, §4.3 (estimate "months", SPECULATIVE).
- Mathlib: same rev 56a0058 as ~/dzq-wt/cr3-check/.lake/packages/mathlib; grep there (no fetch).
