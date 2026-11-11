# h-v16-adopt: report

Branch `wip/h-v16-adopt`. Edited: `docs/research/h-trust.md`, the module docstring of
`ZInQKernel/Hypotheses/Height.lean` (comments only), the H row of `KERNEL_PLAN.md`, and
`scratch/h-v16-adopt/` (log, reruns, `strip_compare.py`). `HeightMin.lean` is unchanged.

## Changes, by h-trust step
- **F1** (rv-up §3.5 item 1). Lin–Yang eq. (2) is no longer a supplier: Lin–Yang attribute it
  to Baba–Granath Prop. 3.9, which rests on Prop. 3.7, and upstream records a defect in 3.7's
  printed proof. F1 now rests on four things: Example 30's divisors of `ψ₄` and `χ₁₀` on `X`
  (the one remaining Lin–Yang input); eqs. (13)-(14); the theta expressions (LNY 2015,
  Igusa 1967); and `igusa_check.py`. The constant at P₋₂₄ is checked by
  `scratch/rv-up/endo24.py` and `theta24.py`. All three scripts were rerun with identical
  outputs. Status unchanged: [R]+[S].
- **A2, Summary 2, §2.5** (rv-up §3.5 items 2-4). The Baba–Granath locator is narrowed to
  Thm 2.1, Lemma 3.1 and the §3 datum (not Props 3.7-3.10), and Summary 2 names what is used
  of each paper. §2.5 says eq. (2) was read but is not used. §2.3 gains a row for the two rv-up
  scripts.
- **C8.** The finiteness of the twist now comes from the determinant argument of Version 14
  (V16 L660-667), written in our own words in four steps:
  - `det V₅(A) = χ²` on `G_F`, so `α = det r₅/χ` has `α² = 1` there;
  - `ψ² = α ε_g^{−1}`, so `ψ` has finite image;
  - Kronecker–Weber (Washington Thm 14.1) makes `ψ` a Dirichlet character.

  This drops the local-algebraicity step, so the `conrad-local-characters` row of §2.4 and
  rv-h-c8 R4's inertia remark go. Kato 2004 (§9.4, p. 188, with §6.3, §§5.4, 8.3 and
  (14.10.2)-(14.10.3)) is added as an all-levels supplier for (HT). (HT) and Kronecker–Weber
  are still needed (rv-up §2.3). Status [M]; the review list adds rv-up §2.3 and up-h §4.
- **C3.** The field is chosen Galois, as in V16 L536-537: a completion at `w | 5` of a Galois
  number field containing `L'`. Repair R1 is therefore not needed. The Fontaine citation is now
  Astérisque 223, pp. 113-184, Thm 3.8, p. 142, which settles the exposé question by page
  range; the content is still unread.
- **A4.** V16's Deligne 1971 locators replace "§§4-6": Prop. 1.15, Thm 4.7, §§4.8-4.17,
  Thm 4.21, Cor. 5.7 and Ex. 5.8, with Deligne 1979 2.2.5 and 2.3.1.
- **E4.** CMH 2014 §2.3 and Cor. 8.4 are added as a second locator; only upstream's model
  reviewer has read them.
- **Counts and residuals.** No step status changes, and the §1 counts stay 7 / 5 / 24 / 0.
  Unrefereed editions and citation swaps go from five to four (Summary 4(e), §2.7(v)). Also
  updated: the script list (Summary 4(d), §2.3, §2.7(iv)), the route table, §2.1, §2.5
  items 3, 6 and 11, the §3 drafts, §4, and the header. A dated changelog entry is at the end.
- **Lean comments and KERNEL_PLAN.** In the Height.lean docstring, the (HT) supplier now reads
  "Saito 1997, Scholl 1990 with Scholze 2013, or Kato 2004", and "Five citations" becomes
  "Four". Lin–Yang 2020 stays (Example 30 and eqs. (13)-(14) are still used); no Baba–Granath
  Props were added. The KERNEL_PLAN H row gains Kato 2004. The §3 draft in h-trust matches the
  Lean docstring exactly (checked).

## Build
- `strip_compare.py`: with comments and docstrings removed, the old and new Height.lean are
  identical. Height.lean is the only file changed under `ZInQKernel/`.
- `lake build ZInQKernel` succeeded (9919 jobs).
- `lake env lean scripts/print_axioms.lean`: all 61 entries show exactly
  `[propext, Classical.choice, Quot.sound]`.

## Problems
None blocking. The new locators (Kato 2004, Fontaine Thm 3.8, the Deligne 1971 places,
Washington, CMH 2014) are still UNVERIFIED, as h-trust §2.5 records. `h-v14.md` l.335 still
cites Lin–Yang eq. (2); it was out of scope here (rv-up §3.5 leaves it to its owner).
