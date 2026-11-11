# redei-bridge log

- Read Entry/Kernel/RedeiStatement/TYZ/Rank.Statements. Plan: Bridge.lean with OddGClStatement,
  sum transport lemma redeiB_sum_entry (ramSet (dProd B) sums -> sums over B plus z-column),
  redeiB_kernel_iff, gCl_dProd_eq_gBit, redeiFormula_of_oddGClStatement,
  certifiedRankTYZRk_of_oddGClStatement (imports Rank.Statements).
- Built deps: lake build Redei.Kernel Redei.Entry Rank5b.Sec3.RedeiStatement (in progress).
- Bridge.lean compiled after one fix (rwa ... at this ⊢ rewrote the goal too; split into rw at this; exact).
  Replaced deprecated if_pos/if_neg/dif_pos/dif_neg by ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right
  (v4.35 deprecations). No warnings. Axioms of redeiFormula_of_oddGClStatement and
  certifiedRankTYZRk_of_oddGClStatement: propext, Classical.choice, Quot.sound.
- Added import line to ZInQKernel/RouteK/Redei.lean.
- Full lake build ZInQKernel OK. Report written.
