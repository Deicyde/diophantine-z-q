---
article_id: af_151513ff830bae631d1b2d55
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Size.padicValRat_coords_ge
---

# Rational coordinates at odd primes

Let $p$ be an odd prime, $k\in\mathbb Z$, and $u=u_0+u_1s\in K_0$ with $u_0,u_1\in\mathbb Q$.
If $v_{\mathfrak p}(u)\ge k$ for every prime $\mathfrak p$ of $\mathbb Z[s]$ containing $p$
(with $v_{\mathfrak p}(0)=+\infty$), then
$$v_p(u_0)\ge k\qquad\text{and}\qquad v_p(u_1)\ge k$$
(with $v_p(0)=+\infty$).

**Proof sketch.** Let $\bar u=u_0-u_1s$. Conjugation permutes the primes above $p$, so
$v_{\mathfrak p}(\bar u)=v_{\bar{\mathfrak p}}(u)\ge k$ for every $\mathfrak p\mid p$. Then
$u_0=(u+\bar u)/2$ and $u_1=(u-\bar u)/(2s)$, and $v_{\mathfrak p}(2)=v_{\mathfrak p}(s)=0$ since
$p$ is odd, so $v_{\mathfrak p}(u_0),v_{\mathfrak p}(u_1)\ge k$ for any one prime
$\mathfrak p\mid p$. For a rational number $c$, $v_{\mathfrak p}(c)=v_{\mathfrak p}(p)\,v_p(c)=v_p(c)$
because $v_{\mathfrak p}(p)=1$.

The manuscript performs the same extraction ("both rational coefficients lie in
$N_s^4\mathbb Z_{(N_s)}$") without spelling it out.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../../model/field/quadratic-field.md)

## Proof depends on

- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](../../multiplication/local/primes-above-p.md)

## Sources

- [Proof of Proposition 12.1, formal multiple](../../../sources/size-locators.md#proof-of-proposition-121-formal-multiple)
