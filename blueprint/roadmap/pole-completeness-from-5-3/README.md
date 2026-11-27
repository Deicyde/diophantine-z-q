---
article_id: af_c1605d3922671d7aec32be48
---

# Pole completeness from the restricted converse

This chapter belongs to Elliot's route to the pole input. Section 5.1 of the manuscript derives
[pole completeness](../statements/pole-completeness.md), its Theorem 5.2, from the restricted converse,
[Theorem 5.3](../restricted-converse/restricted-converse.md), by a simultaneous 2-descent on the curves
$E_\ell:y^2=x(x-\ell)(x+3\ell)$. The other route to the pole input is
[the congruent-number route](../route-k/README.md).

- For an input $B$ the descent chooses a positive divisor $m$ of $2730$ so that $A=mB$ is a square at $2$
  and lies in a nonsquare unit square class at $3$, and takes the positive squarefree parts $\beta$ and
  $\theta$ of $A$ and $H=A(A-B^2)$.
- It builds a positive squarefree $n$, with $n\theta$ squarefree and $n,n\theta\equiv11\pmod{12}$, such that the
  2-Selmer groups of $E_n$ and $E_{n\theta}$ have dimension $3$ and contain the Kummer class $(\beta,1)$ in the
  coordinates $(x+3\ell,x-\ell)$.
- Lemma 5.4 turns dimension $3$ into $2^\infty$-Selmer corank $1$ through the Cassels–Tate pairing, so
  Theorem 5.3 gives analytic rank $1$; the rank half of Lemma 5.5 then gives rank $1$ for both curves.
- The class $(\beta,1)$ then comes from a rational point on each curve, and rescaling the two points gives
  the witnesses of the pole polynomial.

The derivation is formalized in `ZInQKernel/Contrib/PoleRC/`, `ZInQKernel/Contrib/OneProof/PoleS12/` and
`ZInQKernel/Contrib/OneProof/PoleCompletenessFromRC*.lean`, with Lemma 5.4 in
`ZInQKernel/Contrib/OneProof/SelmerCorankFam.lean` and `ZInQKernel/Contrib/OneProof/Lemma54FromCasselsTate.lean`,
the Kummer identification in `ZInQKernel/Contrib/OneProof/KummerSelmerMProof.lean`, and the last step in
`ZInQKernel/Contrib/OneProof/CasselsTatePairing.lean`. The theorem that
`ZInQ.OneProof.frozenTarget` uses is `ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne`. It
leaves three inputs: Theorem 5.3, the Cassels–Tate pairing on the curves $E_\ell$, and Silverman's
rank-one implication (AEC, Appendix C, Evidence 16.5.5), the hypotheses `hRC`, `hCT` and `hRank`. Three steps
differ from the manuscript's text:
- the manuscript leaves the construction of $n$ to its supplementary files S11 and S12; the Lean proof
  follows S12;
- the manuscript uses the finiteness of the Tate–Shafarevich group to conclude that its 2-part vanishes;
  the Lean proof uses only the rank and counts the image of the Kummer map instead;
- for that rank the manuscript's Lemma 5.5 cites modularity with Kolyvagin's theorem; the Lean proof takes
  the rank-one line of Silverman's display instead.

- [The cited inputs: the Cassels–Tate pairing and Silverman's rank-one implication](cited-inputs.md)
- [Lemma 5.4 from the Cassels–Tate pairing](lemma-5-4.md)
- [The simultaneous construction](simultaneous-construction.md)
- [CR_M from Theorem 5.3, Lemma 5.4 and Lemma 5.5](crm.md)
- [Theorem 5.2 from CR_M and the simultaneous construction](pole-completeness-from-crm.md)
- [Theorem 5.2 from Theorem 5.3](pole-completeness-from-5-3.md)
