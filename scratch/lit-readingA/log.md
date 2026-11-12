# lit-readingA results log

## Step 1 (Lean)
- Added `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier`
  (hH : SixContactMin) (hA : Literature.TYZThm35ReadingA) (hC : Literature.HeckeContinuation)
  (hF : Literature.FunctionalEquation5) (hG : Literature.GrossZagier) : FrozenTarget,
  proof: the `tyzRow5b` headline applied to `Literature.tyzRow5b_of_readingA hA hC`.
  File ZInQKernel/MainLiterature.lean; module docstring bullet added. Added to scripts/print_axioms.lean.
- `lake build ZInQKernel`: VERIFIED, "Build completed successfully (9925 jobs)", 6m38s, 2026-11-12 01:12 PST.
- `lake env lean scripts/print_axioms.lean`: VERIFIED, rc 0, 92 `#print axioms`, all 92 report
  exactly [propext, Classical.choice, Quot.sound], including the new theorem. Output: print_axioms.out.

## Step 2 (README.md, KERNEL_PLAN.md)
- Headline switched to the `tyzThm35ReadingA_heckeContinuation` variant in both files; TYZ input stated
  as the leaves `Literature.TYZThm35ReadingA`, `Literature.HeckeContinuation`, bridge
  `Literature.tyzRow5b_of_readingA`, intermediate `Literature.TYZRow5b` and its theorem kept.
- Journal facts used, all from docs/research/locators.md (AI audit with web access, not human):
  arXiv Thm 1.2 = journal Thm 1.4 (pp. 723–724); the all-`d_i > 1` restriction is kept in the journal,
  so 26565 and 33117 refute the journal statement read literally too; convolution lemma = Lemma 2.9
  in both versions (Lemma 2.8 = symmetry lemma); Prop 3.4 proof pp. 751–753 (journal).
- Lemma 2.9 (arXiv v1): VERIFIED from ~/tyz-src/Period7.tex theorem counters: section 2 environments
  sharing the `thm` counter are at L554 (2.1), L571 (2.2), L580 (2.3), L613 (2.4), L646 (2.5),
  L809 (2.6), L842 (2.7), L1009 (2.8, symmetry `P(d1,d2)=P(d2,d1)`), L1062 (2.9, the convolution).
  The repository's `LemmaTwoEight` (TYZInputs.lean, I2) and nt-tyz's "Lemma 2.8" are this Lemma 2.9
  (locator only; not edited, outside this task's files).
- `𝓛(n) = 0` iff `ord_{s=1} L(C_n, s) > 1`: VERIFIED, TYZ definition L338–344.
- "Prop 3.4 proof only sketched": stated for the arXiv version (nt-tyz.md summary 3); the locator audit
  read the journal proof pages but does not comment on completeness, so the README says "in the arXiv version".
- Rebuild after reflowing the MainLiterature module docstring: VERIFIED, build OK (9925 jobs),
  print_axioms rc 0, 92/92 lists exactly [propext, Classical.choice, Quot.sound] (01:17 PST).

## Step 3 (cold read of the README diff)
- Independent cold read (fresh AI agent, read-only, given only the README section and diff) returned
  12 items; all applied in substance:
  1–2 referent errors fixed ("the last two" pointed at FunctionalEquation5/GrossZagier in the theorem
  signature; now names TYZThm35ReadingA and HeckeContinuation); 3 T5aCl/T5bCl block conditions stated
  (from Admissible5aNat / Admissible5bNat) and values in ℤ/2; 4 `d₁` introduced, reading A's two
  sums = T5aCl and T5aCl + T5bCl (nt-tyz §1.3); 5 "It" referent fixed; 6 the 𝓛(n)=0 case is now
  attributed to the paper's Theorem 3.5 (first assertion) + Lemma 3.18 via nt-tyz §2.2 F6;
  7 "we" replaced by "the project's literature search, which AI agents carried out", Smith 1603.08479
  named as the one unrefereed statement; 8 "these criteria" antecedent fixed, counterexample
  evidence stated (exact computation, not in Lean, nt-tyz §1.4); 9 journal proof of Prop 3.4 "not
  assessed"; 10 Lean checks Prop N only from the encoding TYZInputs, encoding fidelity not checked,
  Lemma 2.9 vs the repository's "Lemma 2.8" name; 11 "split up" replaced, FunctionalEquation5
  supplier caveat from locators row 112 added; 12 HeckeContinuation: positive d, Re s > 3/2, original
  Deuring–Hecke source not read by the locator audit (locators "source-access limits").
- KERNEL_PLAN: same encoding caveat (item 10) added.
