---
article_id: af_7c83104d95cef05687abbc90
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.PoleRC.poleCompleteness_of_crm
---

# Theorem 5.2 from CR_M and the simultaneous construction

$\mathrm{CR}_M$ and the simultaneous construction imply pole completeness, the manuscript's Theorem 5.2.

**Proof sketch.** Let $B$ be an admissible input. The bookkeeping chooses a positive divisor $m$ of $2730$
so that $A=mB$ is a square at $2$ and lies in a nonsquare unit square class at $3$, and takes the positive
squarefree parts $\beta$ of $A$ and $\theta$ of $H=A(A-B^2)$; they satisfy the hypotheses of the
simultaneous construction. The construction gives $n$, and then $n\theta\equiv11\pmod{12}$ too. $\mathrm{CR}_M$
at $n$ and at $n\theta$ gives rational points of $E_n$ and $E_{n\theta}$ in the class $(\beta,1)$. Rescaled to
abscissas $A$ and $Az^2$, they give the witnesses of the pole polynomial.

## Depends on

- [Pole completeness](../statements/pole-completeness.md)
- [CR_M from Theorem 5.3, Lemma 5.4 and Lemma 5.5](crm.md)
- [The simultaneous construction](simultaneous-construction.md)

## Sources

- [Theorem 5.2](../../sources/manuscript.md#theorem-52)
- [Section 5.1](../../sources/manuscript.md#section-51)
