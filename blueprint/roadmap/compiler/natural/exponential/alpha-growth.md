---
article_id: af_89688e04748daefa0f2a5b97
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.AlphaPower.alphaZ_growth, ZInQ.AlphaPower.alphaZ_exponential_bounds
---

# Growth of the alpha sequence

Let $b\ge2$ be a natural number and $U_n=\alpha_b(n)$. Then for every $n\in\mathbb N$
$$0\le U_n,\qquad U_n+1\le U_{n+1},\qquad n\le U_n .$$
In particular the sequence is strictly increasing and $U_n\ge1$ for $n\ge1$. Moreover, for
all natural $c\ge1$ and $n$,
$$c^n\le\alpha_{c+1}(n+1),$$
and for $b\ge3$, $\alpha_b(n+1)\le b^n$.

The manuscript states the first group of inequalities for $b\ge3$; the proof works for
$b\ge2$, and $\alpha_2(n)=n$ shows that $b=2$ is the boundary case.

**Proof sketch.** Joint induction on $n$ for the pair $0\le U_n$, $U_n+1\le U_{n+1}$: the
base is $U_0=0$, $U_1=1$; in the step,
$U_{n+2}-U_{n+1}=(b-2)U_{n+1}+(U_{n+1}-U_n)\ge0+1$ because $b\ge2$ and $U_{n+1}\ge0$.
Summing the increments gives $U_n\ge n$. For $c^n\le\alpha_{c+1}(n+1)$ induct on $n$ using
$\alpha_{c+1}(n+2)=(c+1)\alpha_{c+1}(n+1)-\alpha_{c+1}(n)\ge c\,\alpha_{c+1}(n+1)$, which
holds because $\alpha_{c+1}(n)\le\alpha_{c+1}(n+1)$. The upper bound
$\alpha_b(n+1)\le b^n$ is the same induction with $\alpha_b(n+2)\le b\,\alpha_b(n+1)$.

## Depends on

- [The alpha sequence](alpha-sequence.md)

## Sources

- [Section 10.2 alpha recurrence](../../../../sources/compiler-natural-locators.md#section-102-alpha-recurrence)
- [AFP DPRM development](../../../../sources/compiler-natural-locators.md#afp-dprm-development)
