# pb-p1 (2026-11-17): P1 cleared — Pan and Berger both over Fontaine's B_st as printed

**Verdict.** Objection P1 (the leaves' `B_st = B_max[log p~]` is neither Berger's nor Fontaine's ring) is cleared
without comparing rings and without B1:

* Pan's hypothesis is "pst in the sense of Fontaine" (arXiv:1901.07166v2 p. 2).
* Berger's own survey (arXiv:math/0210184v1) prints Fontaine's ring concretely and prints Berger's theorem over it.
  The ring is `B_cris^+ = {Σ x_n ω^n/n!}` (II.3.1), with `B_st = B_cris[log p~]` and `log_p(p) = 0` (II.3.3).
  The theorem is IV.5.1, with the proof in IV.5.3.
* That ring is built in Lean, and both leaves are restated over it: `BergerSurveyF` and `PanPrintedF`, both rated
  printed form, flagged unread.
* `r11r12 : PanBerger` (de Rham hypothesis) follows directly: `panBerger_of_F`. No comparison of rings is used.

**Compiles (standard axioms).**

* `ZInQKernel/Contrib/OneProof/PanBergerFontaine.lean` proves:
  * `A_cris` is a ring and `B_cris^+` equals the printed set;
  * `A_cris` does not depend on the generator and lies in `A_max`;
  * `B_st^F ⊆` the tree's `B_st`, and `B_st^F` is G-stable;
  * basis-form admissibility is monotone in the ring;
  * `bergerPrintedV_of_survey` and `panBerger_of_F`;
  * B1's algebraic half (`bmax_adjoin_eq_bst`).
* `#discharges`: `bergerPrintedV` is discharged by `bergerPrintedV_of_survey`.
* Autofold spec `scratch/pb-p1/autofold.json` (`bergerPrintedV` → `bergerSurveyF`): its dry run compiles, count
  5/29 → 5/29.
* Recommended manual fold `scratch/pb-p1/BypassFold.lean` (`gen_bypass.py`) replaces both `panPrintedP` and
  `bergerPrintedV` (PBP1 copies of generations 40..45, `r11r12 := panBerger_of_F`). It compiles.
* In the bypass fold, `r11r12`'s two rows are GLUE only because they are unread, and no new glue is added.

**Remains.**

* The literal old field `panPrintedP` needs `BmaxStToFontaine` (tree-ring pst ⇒ Fontaine pst). It is not printed
  for `B_max[log p~]` and needs Frobenius machinery. It is recorded as a non-leaf and used in no fold.
* B1 is not formalized. Berger's §1.2 formula for `log[π̄]` divides by `π̄^(0) ∈ C_p`, which is not literal in
  `B_dR^+`. An on-the-spot sketch is in the report §4. B1 is not needed on the route.
* Report: `docs/research/pb-p1.md`.

Final commit 2026-11-17 ~05:20 PST; build logs trimmed to their tails.
