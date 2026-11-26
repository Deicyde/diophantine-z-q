---
article_id: af_0801523fc56d54ae362f2d73
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Wiring.restrictedConverseGenuine_of_leaves
---

# Theorem 5.3 from the cited results and the remaining hypotheses

[The cited results](printed-results.md) and [the remaining hypotheses](remaining-hypotheses.md) imply
[Theorem 5.3](restricted-converse.md).

The remaining hypotheses are not proved, so this theorem does not yet discharge Theorem 5.3:
`ZInQ.OneProof.frozenTarget` still takes Theorem 5.3 itself as the hypothesis `hRC`.

The proof goes through the top-level assembly `ZInQ.Contrib.CloudB3RC53.restrictedConverseGenuine_of_nodes`,
which takes the cited results and two nodes. One of them, the branch package, is equivalent to Theorem 5.3
given the cited results, so the reduction to the manuscript's steps is the theorem stated here.

**Proof sketch.** Fix an admissible $\ell$ with Selmer corank one. The opening reduction gives root number
$-1$, so $L(E_\ell,1)=0$. The proof then splits as in the manuscript. If the odd symbol is a unit at the
empty configuration, visibility at $D=1$ gives a simple zero at once. Otherwise a companion $k$ with
$L(E^{(k)},1)\ne0$ is fixed, and the fixed-field package of Sections 7–9 and Appendices E–G, built from the
remaining hypotheses, gives the clearing identity, a uniform upper bound at every nonzero address and the
base-zero lemma. The missing-address argument (proved) then shows $L'(E/K,1)\ne0$, and since
$L(E/K,s)=L(E,s)L(E^{(k)},s)$ the zero of $L(E_\ell,s)$ at $s=1$ is simple.

## Depends on

- [Theorem 5.3: the restricted converse](restricted-converse.md)
- [The cited results](printed-results.md)
- [The remaining hypotheses](remaining-hypotheses.md)

## Proof depends on

- [The opening reduction: root number $-1$](opening-reduction.md)

## Sources

- [Theorem 5.3](../../sources/manuscript.md#theorem-53)
- [Section 9](../../sources/manuscript.md#section-9)
