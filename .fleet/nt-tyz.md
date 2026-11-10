# nt-tyz report: the Tian–Yuan–Zhang citation behind CR₃

Deliverable: `docs/research/nt-tyz.md`. Scripts and log: `scratch/nt-tyz/`.

## Summary

- **Versions.** TYZ (arXiv:1411.4728) has only v1. The journal version (Asian J. Math. 21 (2017)
  721–774, DOI 10.4310/ajm.2017.v21.n4.a5) could not be read. Crossref registers no erratum. No
  readable version states the form CR₃ uses (`n ≡ 5`, `T_5b(n)` odd ⟹ `𝓛(n) ≠ 0`) directly.
- **The literal Theorem 1.2 is false.** With "all `d_i > 1`", the second sum for `n ≡ 5` is
  `T_5a + g(n) + T_5b`. For `n = 26565` and `n = 33117` it is odd although `rank C_n(ℚ) = 3`
  (exact descent: Kummer images of rank 5), so `𝓛(n) = 0`. The reading with `d₁ > 1` distinguished
  fails on the same two values. Only reading A (`d₁ = 1` admitted, so the sums are `T_5a` and
  `T_5a + T_5b`) is true. It contains the form used. Theorem 3.5(2) omits the `d_i > 1` sentence,
  and Proposition 3.4's proof uses `d₁ = 1`, so reading A is what the authors meant.
- **The proof in §3.3.** Its final step separates the `(7, 3)` bracket from the `(5, 1)` bracket
  (checked). Its coefficients, however, come from Proposition 3.4. That proposition is proved by a
  sketchy joint induction over all classes, and its statement has the same ambiguity. tyz-5b's two
  implicit facts are right. Four more implicit facts are needed and are true: `β` fixes `ℚ(i)`;
  `[i]` commutes with `β'`; `ℍ'_n` is Galois over `ℚ`; and the unproved "i.e." of Theorem 3.5(2) is
  not needed.
- **Self-contained proof (Proposition N).** A parity count over chains of divisors, with a
  swap involution and odd Fubini numbers, shows that the genus point satisfies
  `P(n) ≡ Σ_{e≡5,7} 𝓛(n/e) Z(e) (mod 2)` directly from its defining recursion. This bypasses
  Proposition 3.4. The inputs are TYZ Theorem 3.5 (first assertion), Lemmas 2.8, 3.16, 3.18, 3.21,
  Proposition 2.3 and the recursion of §3.1, all unambiguous. Lemma 2.8 also fixes the
  set-partition reading of Theorem 1.1. The proof gives reading A for `n ≡ 5` in full, and proves
  tyz-5b's SPECULATIVE remark on the `(5, 1)` bracket. Checked on 400 abstract configurations
  (0 mismatches) and on 30 random real `n`.
- **Other sources.** Only Smith (arXiv:1603.08479, Theorem 2.1, unrefereed) states the form
  (reading A, rows 5a and 5b separate). Tian's ICCM Notices 2017 and ICM 2022 articles could not be
  read. Six citing papers and three related papers do not restate the theorem. Zhang cites a
  "Corollary 1.3" of the journal version, which suggests the journal numbering differs from arXiv v1.
- **Kriz.** Not needed for any `d` covered by CR₃: tyz-5b Corollary 4.4 covers all of them, not just
  the slot curves.
- **Unrefereed sources in CR₃'s chain.** The manuscript's Kolyvagin citation is the MPIM preprint
  MPI/90-69 (Lemma 5.5, A020). TYZ themselves cite Kolyvagin's published papers. The others are
  Smith (now unused), Kriz (alternative only), BCDT through the authors' manuscript (not needed for
  CM curves), the project notes (automated review only), and TYZ read in its arXiv form only.

## Ranking

1. Cite Proposition N with the proof of nt-tyz §4. Payoff: no dependence on the false literal
   statement or on Proposition 3.4. Obstacle: needs human review. Test: independent re-derivation
   plus own recomputation of the coefficients on ≥300 configurations. Chance: high.
2. Replace Kolyvagin MPI/90-69 by refereed sources (Gross–Zagier, Kolyvagin Izv. 1989, and an
   auxiliary non-vanishing theorem). Chance: high.
3. Read Tian's ICM 2022 article or the ICCM Notices article, or ask the authors (Jack's call).
   Chance: medium.
4. Compare the journal text of Theorems 1.2, 3.5(2) and Proposition 3.4. Chance: medium.
5. Move the 𝔽₂ half of CR₃ (tyz-5b Theorem 4.3) into Lean. Formalization is feasible, but it would
   barely reduce what has to be trusted. Chance: low.

Eliminated: strengthening the descent to use the literal Theorem 1.2 (it is false), and classical
criteria for one or two primes.

## Open questions

- Does the journal version state Theorem 1.2 with `d₁ = 1` admitted, or with "all `d_i > 1`"? Is its
  numbering the same as arXiv v1?
- Do Tian's expository articles restate the `n ≡ 5` criterion, and in which form?
- Which refereed statement should replace Kolyvagin MPI/90-69 in Lemma 5.5?

## Suggested follow-up tasks

- **Referee nt-tyz §4.** A fresh reviewer re-derives Lemmas N1 and N2 and facts F3–F5 by hand and
  recomputes the coefficients with their own code.
- **Update CR₃'s trust statement and tyz-5b.** Cite "Theorem 3.5 and the argument of the proof of
  Theorem 3.5(2), as completed in nt-tyz §4", drop Theorem 1.2, and note the counterexample
  `n = 26565`. These are edits to Lean comments and notes, for Jack to approve.
- **Kolyvagin citation.** Find and check a refereed source for the forward rank-one theorem used by
  Lemma 5.5 and record it in audit A020.
- **Journal and expository texts.** Obtain AJM 21(4) 721–774 and Tian's ICM 2022 article (open
  access) and compare them with nt-tyz §1.2.
