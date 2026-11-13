---
article_id: af_6426f4c23d00c0054e4b3557
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.poleCompleteness_of_certifiedRank
---

# Pole completeness from the certified rank hypothesis

Assume the certified rank hypothesis CR₃. Then pole completeness holds: every admissible $B$
satisfies $\Phi(B)$, for the pole polynomial with the congruent number curves
$y^2=x(x-\ell)(x+\ell)$.

**Proof sketch.** Let $B$ be admissible. The descent lemma gives $m$ and $n$. Apply CR₃ to
$d=|n|$ and to $d=|n\theta|$, with $a=\beta$ in both cases: $d$ is squarefree with
$d\equiv5\pmod8$, $\beta$ is squarefree (a squarefree part of the nonzero rational $mB$), divides
$n$ and $n\theta$, has $|\beta|\equiv7\pmod8$, and the Selmer certificates are the remaining
hypotheses. This gives rational points with nonzero abscissas in $\beta\mathbb Q^{*2}$ on
$C_{|n|}$ and on $C_{|n\theta|}$, which is $C_{N\theta}$ for $N=|n|$ since only $d^2$ enters.
Since $0<B<1/2$, the integer $m$ is not $B$, so the lemma on points and pole solubility gives
$\Phi(B)$.

## Depends on

- [The certified rank hypothesis](../main/certified-rank.md)
- [Pole completeness](../main/pole-completeness.md)

## Proof depends on

- [The descent lemma](descent-lemma.md)
- [Points on two congruent number curves give pole solubility](points-pole-solubility.md)

## Sources

- [The Lean plan](../../sources/route-k-locators.md#the-lean-plan)
