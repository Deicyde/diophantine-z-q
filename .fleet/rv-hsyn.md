# rv-hsyn: fleet report

**Verdict on docs/research/h-decomposition.md: ANNOUNCEABLE AFTER REPAIRS.** The full report, with
the exact replacement text for each repair, is docs/research/rv-hsyn.md.

**Must fix before 01:00:**
1. §0 TYZ: "with the hypothesis weakened to 𝓛(n) = 0" says the opposite of what is meant. It
   should say that the Lean form uses only the case 𝓛(n) = 0, a special case of the printed
   hypothesis that avoids the unproved "i.e." of Thm 3.5(2) (nt-tyz F6). The same word is in the
   docstring in CR3Literature.lean L137-139, which is outside this task's write scope.
2. §3 calls route K's GK1 and GK2 "NEW and unreviewed". That contradicts §0, §1 and §6 R3, which
   say they were verified by the rv-routek review.
3. §0 says B2-B3 are proved "from four textbook leaves". The proved theorem uses glue-descent's
   cochain forms `LeafHasse` and `LeafLocalTwo`, which are not the T14/T15 Props in the leaf bundle.
   Their derivation from those Props is unproved glue (WP3).

**Smaller repairs:** list the three other `sorry`s in §0; count 20 glue steps plus the composition
G0, not 21; scale down "the whole arithmetic of PR(i) and NoCM"; state the refereed status of the
Séminaire Bourbaki and SGA sources (R1, R14, R21, R6, R8, T1, T2), which weakens §1's reason (i);
the T29 placeholder wording; how R11 and R12 are counted; R15 needs T25 as an input.

**What compiles (VERIFIED):**
- `lake build ZInQKernel.Hypotheses.JHeight` and `lake env lean scratch/h-decomposition/Leaves.lean`
  both succeed.
- The counts are right: 35 of 54 leaves and 39 Props are genuine `def`s with content. The 19
  `opaque` placeholders are exactly the ones the note lists.
- 35 theorems that the note calls proved use only `propext`, `Classical.choice` and `Quot.sound`
  (`scratch/rv-hsyn/LeavesCheck.lean`, `check.out`).
- `sorryAx` occurs only in `glueOutputs_of_leaves` (and so in `sixContactMin_of_leaves`),
  `goodReduction_of_QM_rational3`, `artinConductor_le_of_upper` and `sq_principalUnits`.
- `sixContactMin_of_leaves : ResearchLeaves → TextbookLeaves → ZInQ.SixContactMin`: the
  conclusion is the repository's own `SixContactMin`.

**Not checked:** the Lean bodies of R4, R6, R10, `PanBerger`, T1-T4, T16, T22 and T24-T28 against
their published statements; the locators in §2.2; §4 and §5 in detail.
