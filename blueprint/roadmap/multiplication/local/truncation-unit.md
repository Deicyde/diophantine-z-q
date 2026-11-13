---
article_id: af_7b3f1cbb78ee994d9a2ce823
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.truncLog_eq_mul_unit, ZInQ.Mult.log25_eq_mul_unit, ZInQ.Mult.log25_ne_zero
---

# The truncated logarithm is $16575z$ times a unit

Let $\mathfrak p$ be any nonzero prime of $\mathbb Z[s]$ (including $(s)$), with normalized
valuation $v_{\mathfrak p}$ on $K_0$. For every $z\in K_0$ with $v_{\mathfrak p}(z)\ge1$,
$$L(z)=16575\,z\,(1+\eta),\qquad v_{\mathfrak p}(\eta)\ge2 .$$
In particular $L(z)\ne0$ whenever $z\ne0$ and $v_{\mathfrak p}(z)\ge1$ for some $\mathfrak p$.
The same holds, with the same proof, for $z$ in the completion of $K_0$ at $\mathfrak p$.

**Proof sketch.** $\eta=\sum_{j=1}^{6}(c_j/16575)\,d^{2j}z^{4j}$ with the integer coefficients
$c_j$ of $L$. Here $v_{\mathfrak p}(c_j)\ge0$, $v_{\mathfrak p}(d)\ge0$ since $d\in\mathbb Z[s]$, and
$v_{\mathfrak p}(16575)\le2$: it is $0$ at $(s)$ and at every prime above a rational prime
not dividing $16575=3\cdot5^2\cdot13\cdot17$, and $v_p(16575)\le2$ at the primes above
$p\in\{3,5,13,17\}$, which are unramified. Hence each term has valuation at least
$4j-2\ge2$.

## Depends on

- [The truncated logarithm template](../../syntax/templates/template-log25.md)

## Proof depends on

- [The coefficients of the truncated logarithm](logarithm-coefficients.md)
- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](primes-above-p.md)
- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../../model/field/special-primes.md)

## Sources

- [Fixed local clearing](../../../sources/multiplication-locators.md#fixed-local-clearing)
- [Twelve tests](../../../sources/multiplication-locators.md#twelve-tests)
