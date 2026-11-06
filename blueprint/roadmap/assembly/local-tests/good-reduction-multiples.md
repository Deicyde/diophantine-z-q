---
article_id: af_ae379070ab5b68f56ffcaa61
declaration: lemma
origin: background
---

# Multiples enter the formal neighbourhood at a good prime

Let $\pi$ be a prime element of $\mathbb Z[s]$ associate to neither $s$ nor $d$, and let
$q=|\mathbb Z[s]/(\pi)|$. For every $P\in E(K_0)$ there is an integer $m$ with $1\le m\le q^2+1$ and
$[m]P\in E_1(\pi)$.

**Proof sketch.** Write $v=v_\pi$, $f(x)=x^3+Ax$ with $A=-d^2$, and bars for reduction modulo
$\pi$. Since $\pi\nmid2d$, $2$ is a unit at $\pi$ and the discriminant $-4A^3=4d^6$ is a unit, so
$\bar f$ has three distinct roots and $\bar f'(c)\ne0$ at each root $c$.

*Subtraction.* Let $P,Q$ be affine with $v(x_P),v(x_Q)\ge0$ (then also $v(y_P),v(y_Q)\ge0$),
$\bar x_P=\bar x_Q$ and $\bar y_P=\bar y_Q$. Then $P-Q\in E_1(\pi)$. Indeed, if $P=Q$ the difference
is $O$. If $x_P\ne x_Q$, the abscissa of $P+(-Q)$ is $\lambda^2-x_P-x_Q$ with
$\lambda=(y_P+y_Q)/(x_P-x_Q)$ and $v(x_P-x_Q)\ge1$: when $\bar y_P\ne0$, $v(y_P+y_Q)=0$; when
$\bar y_P=0$, $\bar x_P$ is a root $c$ and $y_P^2-y_Q^2=(x_P-x_Q)g$ with
$g=x_P^2+x_Px_Q+x_Q^2+A$, $\bar g=\bar f'(c)\ne0$, so $y_P\ne y_Q$ and $\lambda=g/(y_P-y_Q)$ with
$v(y_P-y_Q)\ge1$. Either way $v(\lambda)\le-1$ and the abscissa has negative valuation. If
$x_P=x_Q$ and $P\ne Q$, then $Q=-P$, $2\bar y_P=0$, so $\bar x_P$ is a simple root, and $P-Q=[2]P$
has abscissa $(f'(x_P)/(2y_P))^2-2x_P$ with $v(f'(x_P))=0$, $v(2y_P)\ge1$.

*Pigeonhole.* If some $[i]P$ with $1\le i\le q^2+1$ lies in $E_1(\pi)$, take $m=i$. Otherwise the
$q^2+1$ points $[1]P,\dots,[q^2+1]P$ are different from $O$ and have $\pi$-integral coordinates. Their
reductions lie in a set of $q^2$ elements, so two of them, $[a]P$ and $[b]P$ with $a<b$, reduce
to the same pair. Then $[b-a]P\in E_1(\pi)$ with $1\le b-a\le q^2$.

This replaces the reduction homomorphism (Silverman VII.2.1) by the one property used.

## Depends on

- [Formal neighbourhoods of the identity](formal-group.md)

## Proof depends on

- [Valuations of the quadratic field](k0-valuations.md)
- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../../model/field/special-primes.md)

## Sources

- [Lemma 11.2](../../../sources/assembly-locators.md#lemma-112)
- [Silverman](../../../sources/assembly-locators.md#silverman)
