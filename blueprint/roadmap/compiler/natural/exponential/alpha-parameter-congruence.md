---
article_id: af_3071bf0a1b9b49eb0b464de2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.AlphaPower.alphaZ_modEq_of_modEq, ZInQ.AlphaPower.alphaZ_modEq_index
---

# Parameter congruence of the alpha sequence

Let $b,b',d$ be natural numbers with $b\equiv b'\pmod d$. Then for every $n\in\mathbb N$
$$\alpha_b(n)\equiv\alpha_{b'}(n)\pmod d .$$
In particular $\alpha_2(n)=n$ for every $n$, and therefore
$\alpha_b(n)\equiv n\pmod d$ whenever $b\equiv2\pmod d$.

This is congruence in the parameter, not merely between indices: it transports residues
from the parameter $w$ of the alpha formula to the parameters $b$ (modulo $v$) and $2$
(modulo $u$).

**Proof sketch.** Induct on $n$ with the statements for $n$ and $n+1$ together:
$\alpha_b(n+2)=b\,\alpha_b(n+1)-\alpha_b(n)$ and each factor is congruent to its
counterpart for $b'$. For $b=2$ the recurrence $U_{n+2}=2U_{n+1}-U_n$ with $U_0=0$, $U_1=1$
has the solution $U_n=n$. The case $d=0$ is the trivial case $b=b'$.

## Depends on

- [The alpha sequence](alpha-sequence.md)

## Sources

- [Section 10.2 alpha recurrence](../../../../sources/compiler-natural-locators.md#section-102-alpha-recurrence)
