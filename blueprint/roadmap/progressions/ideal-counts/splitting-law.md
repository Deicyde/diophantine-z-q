---
article_id: af_70c61a80fd63807e9c41e9ae
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.localEps_eq_legendreSym, ZInQ.Progressions.idealCount_prime_eq_legendreSym, ZInQ.Progressions.idealCount_prime_pow_eq_legendreSym, ZInQ.Progressions.IdealCount.idealCount_prime_eq_card_ringHom, ZInQ.Progressions.IdealCount.card_ringHom_eq_card_sqrt
---

# The splitting law in $\mathbb Q(\sqrt d)$

Let $K$ be a number field of degree $2$ and $d$ an integer that is not a square, such that
$\mathcal O_K$ contains an element $\alpha$ with $\alpha^2=d$; for instance
$K=\mathbb Q(\sqrt d)$ and $\alpha=\sqrt d$. Let $p$ be an odd prime with $p\nmid d$. Then
the local sign $\varepsilon_p=a_K(p)-1$ is the Legendre symbol:
$$\varepsilon_p=\Bigl(\frac dp\Bigr),$$
so $a_K(p)=1+(d/p)$ and $a_K(p^k)=\sum_{j=0}^k(d/p)^j$ for every $k\ge0$.

The hypothesis that $d$ is not a square cannot be dropped: in $K=\mathbb Q(i)$ with
$\alpha=1$, $d=1$ and $p=3$, the prime $3$ is inert, so $\varepsilon_3=-1\ne(1/3)$.

**Proof sketch.** Ideals of norm $p$ are the kernels of ring homomorphisms
$\mathcal O_K\to\mathbb Z/p$, and distinct homomorphisms have distinct kernels, so $a_K(p)$ is
the number of such homomorphisms. With $t$ the trace from $\mathcal O_K$ to $\mathbb Z$, every
$x\in\mathcal O_K$ satisfies $2dx=d\,t(x)+t(\alpha x)\,\alpha$, as one checks in the basis
$1,\alpha$ of $K$, using $t(\alpha)=0$. Since $2d$ is invertible modulo $p$, a homomorphism
$\varphi$ is determined by $r=\varphi(\alpha)$, which satisfies $r^2=d$; conversely, for each
$r$ with $r^2=d$, the map $x\mapsto(d\,t(x)+t(\alpha x)r)/(2d)$ is a ring homomorphism, by two
trace identities obtained by comparing coefficients in the basis $1,\alpha$. Hence
$a_K(p)=\#\{r\in\mathbb Z/p:r^2=d\}=1+(d/p)$. No Kummer–Dedekind theorem and no index
computation are needed. The formula for $a_K(p^k)$ then follows from the prime-power formula.

## Depends on

- [The quadratic field $\mathbb Q(\sqrt d)$](../quadratic-fields/quadratic-field.md)
- [The ideal counting function](ideal-count.md)

## Proof depends on

- [Ideal counts at prime powers in a quadratic field](local-factors.md)

## Sources

- [Marcus, Chapter 3](../../../sources/progressions-locators.md#marcus-chapter-3)
