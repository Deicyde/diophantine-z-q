---
article_id: af_8296dc8c36f0a8f8d424af83
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.CloudB3RC53.rootNumberNode_proof, ZInQ.Contrib.CloudB3RC53.RootNumberNode
---

# The opening reduction: root number $-1$

Assume [the cited results](printed-results.md). Let $\ell\equiv11\pmod{12}$ be positive and squarefree,
and suppose that $\operatorname{corank}_{\mathbb Z_2}\mathrm{Sel}_{2^\infty}(E_\ell/\mathbb Q)=1$. Then the root
number of $E_\ell:y^2=x(x-\ell)(x+3\ell)$ is $-1$: some entire continuation of $L(E_\ell,s)$ satisfies the
functional equation with sign $-1$ on the strip $0<\operatorname{Re}s<2$.

Hence $\operatorname{ord}_{s=1}L(E_\ell,s)$ is odd
(`ZInQ.Manuscript.RC.PrintsAnalytic.analyticOrder_odd_of_selmerCorankOne`), and the rest of the proof of
Theorem 5.3 excludes analytic rank three or more.

**Proof sketch.** $E_\ell$ has full rational two-torsion, with roots $0,\ell,-3\ell$, so it has a rational
point of order two. The parity theorem of Dokchitser and Dokchitser then turns corank one, which is odd,
into root number $-1$.

## Depends on

- [The cited results](printed-results.md)
- [Theorem 5.3: the restricted converse](restricted-converse.md)

## Sources

- [Section 7](../../sources/manuscript.md#section-7)
