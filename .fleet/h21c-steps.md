# h21c-steps (fleet summary)

**Result.** `h21C` (`TYZGenusFold.TYZThm21PairsC`) is proved equivalent, in Lean, to a new hypothesis
`h21S = ZInQ.Contrib.H21CSteps.TYZThm21Span`: TYZ Theorem 2.1 with `π_ℤ^{U_n}` read through Theorem 2.4(1)
(`π^U = ⊕ ℂ f_δ`, the six forms `f_δ` defined in Lean from L620–622).

The review's cheapest reduction is done:
* `f_δ` is defined in Lean;
* the injectivity of the 8 representatives of Lemma 2.5 is proved (`twoRep_mem_DCU_iff`: hfx-proof's 2-adic step
  with `ω = 0` and a mod-4 `decide`), as is surjectivity for the finer group `ℚ̂^× U`;
* the two 8-sum conditions are proved equivalent to membership in span{f_δ} (`inPiZ_iff_inPiSpan`, character
  orthogonality by `decide`, no measure).

L715–727, Lemma 2.5's measure and `π ⊂ 𝒜₀` are no longer used.

**Blocked.** Splitting into two separately stated hypotheses (Theorem 2.1 and Theorem 2.4(1)) is not possible,
because `π` (the Jacquet–Langlands transfer of `f_E`) has no Lean definition. Theorem 2.4(1) enters only as the
definition of `π^U` inside Theorem 2.1. Net effect: 0 new fields; −1 GLUE if a reviewer rates `h21S` LEAF
(proposed rating LEAF: printed form, with one definition-level reading).

**Compiles** (standard axioms only):
* `ZInQKernel/Contrib/OneProof/TYZThm21Span/FDelta.lean` and `ZInQKernel/Contrib/OneProof/TYZThm21Span.lean`;
* `scratch/h21c-steps/FoldCheck.lean` (`frozenTarget_h21S`, `frozenTarget_h21S'`);
* `#discharges`: `DISCHARGES [h21C] by H21CSteps.tyzThm21PairsC_of_span, still assumes [TYZThm21Span]`.

Fold spec: `scratch/h21c-steps/autofold.json` (manual fold; `h21C` is a top-level argument of `frozenTarget`).
Kinds row: `scratch/h21c-steps/kinds-rows.tsv`.

**Remains:**
* review of `h21S`;
* a `locators.md` row (text in the report, §5);
* the general-`x` formula for `f_δ(1+2x)` and the identity `ℚ̂^×U = ℚ̂^×U4` are not formalized (not needed).

Report: `docs/research/h21c-steps.md`.
