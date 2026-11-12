# lit-readingA: the headline with the Tian–Yuan–Zhang input as "ReadingA + Hecke"

**Result.** The owner's choice for presenting the Tian–Yuan–Zhang (TYZ) input, "ReadingA + Hecke",
is now the fork's headline in Lean and in the two top-level documents:

```lean
theorem ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier
    (hH : SixContactMin) (hA : Literature.TYZThm35ReadingA) (hC : Literature.HeckeContinuation)
    (hF : Literature.FunctionalEquation5) (hG : Literature.GrossZagier) : FrozenTarget
```

(`ZInQKernel/MainLiterature.lean`), proved from the earlier headline
`…_sixContactMin_tyzRow5b_functionalEquation5_grossZagier` through the kernel-checked bridge
`Literature.tyzRow5b_of_readingA : TYZThm35ReadingA → HeckeContinuation → TYZRow5b`. VERIFIED:
`lake build ZInQKernel` succeeds (9925 jobs), and `lake env lean scripts/print_axioms.lean` prints
92 axiom lists, each exactly `[propext, Classical.choice, Quot.sound]`, the new theorem included.

## What changed

1. `ZInQKernel/MainLiterature.lean`: the new theorem with a docstring in its neighbours' style; the
   module docstring lists the two leaves and calls `PropN.TYZInputs` supporting evidence.
   `scripts/print_axioms.lean`: one new `#print axioms` line.
2. `README.md` (fork blockquote) and `KERNEL_PLAN.md` (headline paragraph): the headline is the new
   theorem; the TYZ input is the two leaves `Literature.TYZThm35ReadingA` and
   `Literature.HeckeContinuation` with the bridge `Literature.tyzRow5b_of_readingA`; the
   `TYZRow5b` theorem is kept as the intermediate form. Proposition N (`PropN.TYZInputs`,
   `PropN.tyzThm35ReadingA_of_tyzInputs`) is cited as supporting evidence, not as a leaf. Every
   TYZ caveat is kept: no refereed text that we have read states reading A explicitly; the
   introductory theorem read literally is false (`d = 26565`, `33117`); the proof of Proposition
   3.4 is only sketched (arXiv version); Proposition N has two AI reviews and no human review.
3. Journal facts, from `docs/research/locators.md` (an audit by AI agents with web access, said so
   in both files): arXiv Theorem 1.2 is the journal's Theorem 1.4 and keeps the restriction that
   every factor `d_i` is greater than one, so the two counterexamples apply to the journal version
   too; the convolution lemma is Lemma 2.9 in both versions. `TYZThm35ReadingA` is stated as a
   consequence of Theorem 3.5(2) under reading A that uses only the case `𝓛(n) = 0` of the printed
   hypothesis, which avoids the unproved "i.e." clause.
4. Cold read of the README diff (step 3), by a fresh AI agent given only the README section and the
   diff: 12 items, all applied (list in `scratch/lit-readingA/log.md`). Two were real errors: "the
   last two hypotheses" pointed, in the theorem's signature, at `FunctionalEquation5` and
   `GrossZagier`. The others make the text self-contained: the block conditions of `T5aCl` and
   `T5bCl`; reading A's two sums `T5aCl` and `T5aCl + T5bCl`; the `𝓛(n) = 0` case attributed to
   Theorem 3.5's first assertion and Lemma 3.18 through nt-tyz §2.2 F6. They also remove
   overclaims: "we" replaced by the project's AI-conducted literature search; the counterexamples
   flagged as exact computation, not Lean; the journal proof of Proposition 3.4 "not assessed";
   Lean checks Proposition N only from the encoding `TYZInputs`, whose fidelity is unchecked; the
   `FunctionalEquation5` and Deuring–Hecke source caveats of the locator audit. `KERNEL_PLAN.md`
   was brought in line on the same points.

## Findings (for a later, separately reviewed change; not edited here)

- Lemma 2.9 VERIFIED independently for arXiv v1 from the theorem counters of the TeX source
  (section 2: L1009 is Lemma 2.8, the symmetry lemma; L1062 is Lemma 2.9, the convolution). The
  repository's name `LemmaTwoEight` (`ZInQKernel/Hypotheses/TYZInputs.lean`, input I2) and the
  "Lemma 2.8" of `docs/research/nt-tyz.md` and `PropN.lean` therefore refer to TYZ's Lemma 2.9.
  The mathematical content encoded is unaffected; only the locator is wrong. Those files are
  outside this task's scope.
- `𝓛(n) = 0` exactly when `ord_{s=1} L(C_n, s) > 1`: VERIFIED from TYZ's definition (L338–344), which
  is what lets the Lean hypothesis `2 ≤ analyticOrderAt F 1` stand for TYZ's case `𝓛(n) = 0`.
- Whether the journal's proof of Proposition 3.4 (pp. 751–753) is still a sketch is not stated by
  the locator audit; the documents therefore say "sketched in the arXiv version".

## Files

`ZInQKernel/MainLiterature.lean`, `scripts/print_axioms.lean`, `README.md`, `KERNEL_PLAN.md`;
`scratch/lit-readingA/log.md` (results log), `print_axioms.out` (axiom output),
`readme.diff` and `readme_fork_section.md` (the cold-read inputs).
