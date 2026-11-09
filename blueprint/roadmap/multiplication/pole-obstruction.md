---
article_id: af_6084e6770febd47d6a3e6c37
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Mult.pole_obstruction
---

# The one-sided pole obstruction

Let $S_0=\{2,3,5,7,13\}$ and let $\Phi(B)$ be the rational solubility of the pole polynomial
$Q_{\rm pole}$ with input $B$, as in pole completeness (that article is linked for the
definition of $\Phi$ only; the hypothesis PC is not assumed). If $B\in\mathbb Q$, $B\ne0$ and
$\Phi(B)$, then for every prime $p\notin S_0$ it is not the case that $v_p(B)$ is negative
and odd.

This is Lemma 5.1, for the Route K pole polynomial, whose curves are $y^2=x(x-\ell)(x+\ell)$
instead of the manuscript's $y^2=x(x-\ell)(x+3\ell)$; the statement and $S_0$ are unchanged. It
uses no hypothesis: it is the elementary direction of the pole
predicate, and the multiplication soundness argument uses it at the odd contact primes.

**Proof sketch.** Take a rational zero $(b_0,\dots,b_5,e,z,r_1,r_2,w)$ of $Q_{\rm pole}$ with
input $B\ne0$. Since $B\ne0$ the sum of squares in $Q_{\rm pole}$ vanishes, so every summand
does: $b_i^2=b_i$, hence $b_i\in\{0,1\}$; $eHzw=1$, hence $e,H,z\ne0$; $r_1^2=T_1$ and
$r_2^2=T_2$. The multiplier $m$ is a product of factors in
$\{\pm1\},\{1,2\},\{1,3\},\{1,5\},\{1,7\},\{1,13\}$, so it is a signed divisor of
$2730=2\cdot3\cdot5\cdot7\cdot13$ and $v_p(m)=0$ for $p\notin S_0$.

Suppose $k=v_p(B)<0$ is odd. Then $v_p(A)=v_p(mB)=k$; since $2k<k$,
$v_p(A-B^2)=2k$, so $v_p(H)=3k$. The equations say that $(A,r_1)$ lies on
$C_e:y^2=x(x-e)(x+e)$ and, multiplying $r_2^2=T_2$ by $z^2$, that $(Az^2,zr_2)$ lies on
$C_{eH}$: $(zr_2)^2=z^2T_2=Az^2(Az^2-eH)(Az^2+eH)$. Both abscissas are nonzero ($m\ne0$
because $1-2b_0=\pm1$ and the other factors are positive, and $z\ne0$), and both parameters
$e,eH$ are nonzero. The valuations of $e$ and $eH$ differ by the odd number $3k$, so exactly
one of them is even. If $v_p(e)$ is even, the parity lemma applied to $(A,r_1)$ makes
$v_p(A)=k$ even; if $v_p(eH)$ is even, it makes $v_p(Az^2)=k+2v_p(z)$ even. Both contradict $k$
odd.

## Depends on

- [Pole completeness](../main/pole-completeness.md)

## Proof depends on

- [Parity of the abscissa on $y^2=x(x-\ell)(x+\ell)$](abscissa-parity.md)

## Sources

- [One-sided obstruction](../../sources/multiplication-locators.md#one-sided-obstruction)
- [Pole predicate](../../sources/multiplication-locators.md#pole-predicate)
