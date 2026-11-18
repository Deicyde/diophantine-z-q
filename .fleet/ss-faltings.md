# ss-faltings: summary

**Result: the last SGA 7 row (`sga7_IX_Cor3_3_Def34`, SGA 7 IX Cor. 3.3) is rerouted through Faltings 1983. It
compiles, and the stop rule was not triggered.** The work is on fork main f3402e89 (merged), top
`sixContactMin_of_open76` (TailZ83). Full report: docs/research/ss-faltings.md.

- **What the readers need.** The field reaches the proof only through height-split's SS1-SS3, read by R18, R19,
  R21 (bost-gr9's `r21_of_grBost'`), R22, `StableHeightFinite` and the lower half of R20. These need only two things:
  - (1) Faltings 1983 §1: the height of a semistable Néron model does not change under finite extension. The
    manuscript uses it uncited at diophantine_zq.tex L596-598, and the bibliography has the paper;
  - (2) one field of semistable reduction.

  Semistability of a base change is never used.
- **New leaf:** `faltingsSemistableHeightBC : ZInQ.SSFaltings.FaltingsSemistableHeightBC`, provenance (b), kind
  published. It counts GLUE, flagged "pending reading", because Faltings §1 was not read (no network access; locator
  UNVERIFIED). It follows from SS2 (proved), so it is not stronger than the row it replaces.
- **(2) is proved in Lean** (`semistableReductionThmIF_of_raynaud`): semistable over every number field containing
  `K(A[15])`. It uses Raynaud's criterion with the manuscript's `A[3]`/`A[5]` choice (L814-817, the folded
  `silverbergZarhinThm35`) and textbook fields already in the bundle.
- **Compiles.** Only standard axioms throughout:
  - `ZInQKernel/Contrib/OneProof/SSFaltings.lean`, `SSFaltingsGR9.lean`, and `SSFChain.lean` (the generated chain,
    top `sixContactMin_of_open76_sf`);
  - scratch/ss-faltings/BypassFold.lean, top `HDec.HSyn.sixContactMin_of_open77sf` on `OpenResearchLeaves58SF`.

  The closure check finds no Cor. 3.3, IX 3.3, SS2 or SS3 statement under the new top. `#discharges` shows no field
  discharged outright, so there is no autofold spec. The dead-field probe finds no field that becomes unread.
- **Count on f3402e89:** 29 fields, 5 LEAF / 24 GLUE before and after (strictest 5/24 → 5/24). This becomes 6/23 once
  Faltings §1 is read against the statement. SGA 7 rows: 2 → 1, and 0 after d2a6b's IX 3.5 bypass.
- **Manuscript.**
  - L597-598 ("does not change its stable Faltings height") is uncited. It is filled by Faltings 1983 §1 (ELLIOT-type
    sentence, now a cited print).
  - The stable height (L598, L876) is used without a well-definedness argument. That gap is filled by Raynaud plus
    Faltings, both proved or stated in Lean.
  - At L621, R20 needs a common semistable field for source and target. It is supplied, at `K(A[15])·K(B[15])`.
  - No error found.
- **Remains for the lead.**
  - Fold BypassFold.lean with SSFChain.lean.
  - If d2a6b folds first, rerun TaintS.lean on the new top (two lines), then gen_chain.py and gen_bypass.py. Both
    stop with an error on a missing target.
  - Have Faltings 1983 §1 read: the statement, the height normalization, and "semistable".
  - Known issue: the leaf moves the citation from SGA 7 IX 3.3 to Faltings, who gives SGA 7 IX 3.3 as the reason
    (recalled, UNVERIFIED). The mathematics still rests on it inside the cited print.

Report: docs/research/ss-faltings.md (commit f2a1a8bc); results log scratch/ss-faltings/log.md.
