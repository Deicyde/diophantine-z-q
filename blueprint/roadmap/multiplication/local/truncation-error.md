---
article_id: af_377edb707386c7c29ff0c184
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Mult.log25_truncation_error
---

# The truncation error at a large prime

Let $p>324$ be a prime, $\mathfrak p$ a prime of $\mathbb Z[s]$ above $p$, $K_{\mathfrak p}$ the
completion of $K_0$ at $\mathfrak p$ with valuation $v$ ($v(p)=1$), and $\lambda$ the formal
logarithm of $E$ over $K_{\mathfrak p}$. For every $P\in E_1(K_{\mathfrak p})$ with $P\ne O$:

1. $v(\lambda(P))=v(z(P))\ge1$;
2. $L(z(P))=16575\,\lambda(P)\,(1+\epsilon)$ with $\epsilon\in K_{\mathfrak p}$ and
   $v(\epsilon)\ge28$.

For $P=O$ both sides of (2) vanish.

**Proof sketch.** Put $t=z(P)$, so $v(t)\ge1$, and $\lambda(P)=\log(t)$ is the binomial series.
By the coefficient identity, $\log(t)-L(t)/16575=\sum_{j\ge7}(-1)^j\binom{2j}{j}d^{2j}t^{4j+1}/(4j+1)$.
With $r=4j+1\ge29$, each term relative to $t$ has valuation at least $(r-1)v(t)-v_p(r)\ge
r-1-v_p(r)\ge28$: if $p\nmid r$ this is $r-1\ge28$, and if $p\mid r$ then $r\ge p\ge331$ and
$v_p(r)\le\log_{331}r<r-29$. So $\log(t)-L(t)/16575=t\delta$ with $v(\delta)\ge28$. The terms
$1\le j\le6$ of $\log(t)/t-1$ have valuation at least $4j\ge4$ because $4j+1\le25<p$, and the
tail has valuation at least $28$; hence $\log(t)=t\cdot(\text{unit})$, which is (1). Then
$L(t)/16575=\log(t)(1+\epsilon)$ with $\epsilon=-t\delta/\log(t)$ and $v(\epsilon)=v(\delta)\ge28$.

## Depends on

- [The formal neighbourhood of $y^2=x^3+Ax$ and its filtration](formal-group.md)
- [The formal logarithm](formal-logarithm.md)
- [The truncated logarithm template](../../syntax/templates/template-log25.md)
- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](primes-above-p.md)

## Proof depends on

- [The formal logarithm of $E$ is a binomial series](logarithm-series.md)
- [The coefficients of the truncated logarithm](logarithm-coefficients.md)

## Sources

- [Logarithm series](../../../sources/multiplication-locators.md#logarithm-series)
