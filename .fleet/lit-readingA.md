# lit-readingA (fleet report)

**Result.** The owner's "ReadingA + Hecke" choice is the fork's headline:
`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier`
(`ZInQKernel/MainLiterature.lean`) takes `SixContactMin`, `Literature.TYZThm35ReadingA`,
`Literature.HeckeContinuation`, `Literature.FunctionalEquation5` and `Literature.GrossZagier`. It is
proved from the `TYZRow5b` headline through `Literature.tyzRow5b_of_readingA`.

**What compiles (VERIFIED).** `lake build ZInQKernel` succeeds (9925 jobs, 01:17 PST).
`lake env lean scripts/print_axioms.lean` prints 92 axiom lists, each exactly
`[propext, Classical.choice, Quot.sound]`, the new theorem included (output in
`scratch/lit-readingA/print_axioms.out`).

**Docs.** README.md (fork blockquote) and KERNEL_PLAN.md (headline paragraph):
- the headline is the new theorem;
- the TYZ input is the two leaves with the bridge;
- the `TYZRow5b` theorem is kept as the intermediate form;
- Proposition N (`PropN.TYZInputs`, `tyzThm35ReadingA_of_tyzInputs`) is supporting evidence, not
  a leaf.

Every TYZ caveat is kept. The journal facts come from `docs/research/locators.md`, labelled as an
AI audit with web access:
- arXiv Theorem 1.2 = journal Theorem 1.4, still with every `d_i > 1`, so 26565 and 33117 refute
  both versions;
- the convolution lemma is Lemma 2.9;
- `TYZThm35ReadingA` is a consequence of Theorem 3.5(2) under reading A, using only the
  `𝓛(n) = 0` case, which avoids the unproved "i.e.";
- the proof of Proposition 3.4 is a sketch.

**Cold read.** A fresh agent read the README section and diff and returned 12 items, all applied.
Two were real errors ("the last two hypotheses" had the wrong referent). The rest were clarity
fixes and removed overclaims. Report: `docs/research/lit-readingA.md`. Log:
`scratch/lit-readingA/log.md`.

**Remains (outside this task's files).**
- The repository's "Lemma 2.8"/`LemmaTwoEight` (TYZInputs.lean, PropN.lean, nt-tyz.md) is TYZ's
  Lemma 2.9. VERIFIED for arXiv v1 from the TeX theorem counters.
- nt-tyz.md still says the journal could not be read.
- Whether the journal's proof of Proposition 3.4 is complete has not been assessed.
- `print_axioms.lean` and README/KERNEL_PLAN may conflict textually with other branches at
  integration.
