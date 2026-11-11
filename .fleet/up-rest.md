# up-rest: upstream Versions 13-16 against the fork's other inputs

**Verdict.** Nothing in upstream's Versions 13-16 breaks or weakens a fork statement, and nothing
needs to be adopted. Full note: `docs/research/up-rest.md`. Log: `scratch/up-rest/log.md`.
- Theorem 1.1 is the same text in N5 and in V13-V16 (V16 L113-130; it differs from N5 L60-77
  only in line endings).
- `construction/` and `lean/` are byte-identical to the fork's copies, except their READMEs. This
  includes `ordinary-integer-definition.json` and `lean/Frozen/BoundedIntegerPolynomial.lean`, so
  `FrozenTarget` is unchanged.
- V16 is exactly V15 plus its recorded edits and two amendments. Replaying them byte for byte with
  `scratch/up-rest/v15_to_v16.py` reproduces V16.
- The compiler, bridge and size sections and the catalogue passages are verbatim in V16. The
  source of CAT (BMOR 2018) is unchanged.
- In the Mordell-Weil passage only the class-number justification is reworded. The fork proves
  CAT8 and MW in Lean anyway.
- None of the three V16 corrections touches the fork:
  - The horizontal normalization (V16 L26821-26915) is in upstream's in-manuscript
    inverse-theorem part.
  - The Gaudron-Remond fix (V16 L30664, L30677) is in the 222-variable family. The six-contact
    proof keeps Duke Theorem 1.4 and Section 9, as the fork's notes do.
  - The Tao-Ziegler adaptation and the precision amendment (V16 L20060-20078) concern only the
    quartics' simultaneous-prime input.
- Upstream's theorem-application audit is unchanged. It is now explicitly bound to a copy of N5
  that is byte-identical to the fork's `diophantine_zq.tex`.

**Most important finding.** Upstream still proves the large construction through 22P (Prop. 6.2,
verbatim at V16 L2076). Since V15 it takes the inverse theorem GI(20) from an in-manuscript part
(`v15:gi-full`). Version 16's first correction fills a step there that was "missing at
finite-cover site". So upstream's own justification of 22P had a gap until 11-11. Route AP
(Green-Tao dense plus Proposition D, both Lean theorems) uses no inverse theorem, so it is
unaffected and still applies to every version's large construction. It does not transfer as is to
the quartics' prime input (cross-prime coprimality; SPECULATIVE, as v14-routes.md §5.4 said).

**Single next step.** The owners of KERNEL_PLAN's 22P row, `nt-22p.md` and `v14-routes.md` §2.4
could add one status line: upstream justifies 22P by `v15:gi-full`, corrected in V16, and the
narrowest variant does not depend on it. No Lean change is needed.
