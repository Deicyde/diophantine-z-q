---
article_id: af_da5f38b69bfe3d6aee9db599
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves, ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne
---

# The cited inputs: the Cassels–Tate pairing and Silverman's rank-one implication

Write $E_\ell:y^2=x(x-\ell)(x+3\ell)$. The derivation of Theorem 5.2 from Theorem 5.3 uses two cited
statements besides Theorem 5.3.

- **The Cassels–Tate pairing on the curves $E_\ell$.** For every positive squarefree $\ell\equiv11\pmod{12}$
  there is a biadditive pairing $Ш(E_\ell/\mathbb Q)\times Ш(E_\ell/\mathbb Q)\to\mathbb Q/\mathbb Z$ that is
  alternating and whose kernel is the maximal divisible subgroup of $Ш(E_\ell/\mathbb Q)$. This is Cassels'
  theorem as Poonen and Stoll restate it in their introduction; the manuscript cites it in the proof of
  Lemma 5.4. Because that sentence reports the theorem rather than proving it, the project counts this
  statement as glue until it is re-cited to a source that proves it and that page is read.
- **Silverman's rank-one implication.** For every elliptic curve $E$ over $\mathbb Q$ and every entire
  continuation $F$ of $L(E,s)$ from $\operatorname{Re}s>3/2$, if $F(1)=0$ and $F'(1)\ne0$ then $E(\mathbb Q)$
  has rank $1$. This is the rank-one line of the display in Silverman, *The Arithmetic of Elliptic Curves*,
  2nd ed., Appendix C, Evidence 16.5.5, p. 453, which records the work of Gross, Zagier and Kolyvagin
  and, by the text after it, needs no modularity assumption. It is the rank half of the manuscript's
  Lemma 5.5, the only half the Lean proof uses (`ZInQ.Manuscript.PoleS12.SilvermanRank.rankOne_of_aec`).

Neither is proved here. `ZInQ.OneProof.frozenTarget` takes Theorem 5.3, the pairing and Silverman's
implication as its hypotheses `hRC`, `hCT` and `hRank`.

## Depends on

None.

## Sources

- [Lemma 5.4](../../sources/manuscript.md#lemma-54)
- [Lemma 5.5](../../sources/manuscript.md#lemma-55)
