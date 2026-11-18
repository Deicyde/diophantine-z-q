# pc-from-rc (fork issue #83): Theorem 5.2 from Theorem 5.3

**Result (compiled, only standard axioms):**
`ZInQ.Manuscript.PoleRC.poleCompleteness_of_restrictedConverse_final` in
`ZInQKernel/Contrib/OneProof/PoleCompletenessFromRC.lean` proves `Manuscript.PoleCompleteness`
(Theorem 5.2) from:
- `Manuscript.RestrictedConverse P` (Theorem 5.3);
- `Lemma54At P` (Lemma 5.4 interface; `P` stays abstract);
- the printed leaves `KolyvaginRankOne` (BCDT Thm A + Kolyvagin Thm 1, rank half) and `MordellWeil`;
- `MatrixRealization` (lines 1033–1060; ELLIOT, the manuscript cites S11–S12);
- the four textbook local images `LocalTwo`, `LocalThree`, `LocalBad`, `LocalGood`.

**Proved in Lean** (`ZInQKernel/Contrib/PoleRC/`, about 2700 lines):
- the squareclass bookkeeping and the rescaling to the eleven witnesses;
- `CRM → SimultaneousConstruction → PC`;
- the dimension-three count from the local images, including the `𝔽₂` claim "v = 0, δ = 0,
  u ∈ ker K" for the genuine K, with the reciprocity identities the text omits;
- the complete 2-descent of `E_ℓ` (`descentGlueM`: Kummer homomorphism, halving, ker = 2E,
  `#E[2] = 4`, counting);
- `CRM` from Theorem 5.3 and the lemmas.

**Issues found** (report §0):
- the representative shape and the matrix-forcing claim rest on unstated 2-adic and reciprocity
  facts (now proved or isolated);
- the Boolean-assignment step is a sketch;
- Kolyvagin is cited as a preprint.

No statement was found false.

**Remaining:** `MatrixRealization` (needs a lead decision on completing the construction),
the local images (`LocalGood` sufficiency is the hard part), and `Lemma54At` (Selmer predicate
design).
Report: `docs/research/pc-from-rc.md`.
