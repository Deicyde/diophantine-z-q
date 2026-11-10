---
article_id: af_e105afcdf13adafbd2bc496d
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.lemmaP_three, ZInQ.Mult.padicValRat_traceTheta_of_clear
---

# Lemma P, part (3): the valuation of the pole input

Let $p$ be a prime, $\eta\in\{1,-1\}$, $\ell\in\mathbb Q$ nonzero with $v_p(\ell)\ge0$, and
$t\in\mathbb Q\setminus(\mathcal C\cup\{1\})$ with $R_0=\eta F(t)/(t-1)^8$. Suppose that for some
$e\in\mathbb N$
$$v_p(R_0)=2e,\qquad v_p(t-1)=-e .$$
Let $q\in\mathbb Q$ with $a=1-R_0q^2\ne0$ and
$$v_p(a)\ge23e+v_p(12)+2,$$
and let $D_{gj}\in K_0$ ($1\le g\le6$, $1\le j\le12$) be integral at every prime of
$\mathbb Z[\sqrt2]$ above $p$. Form $R=\ell^2a^2R_0$, $C_{gj}$, $W_g$ and $\Theta$ as in the
slope predicate, and assume $\Theta\ne0$. Then the pole input $B=R/\Theta^2$ has
$v_p(B)\ge4$.

**Proof sketch.** Measure valuations above $p$ on the scale of $v_p$. Then
$v(C_{gj})\ge-2ek_j+e(k_j+1)=-e(k_j-1)$, and $v(R)=2v_p(\ell)+2v_p(a)+2e$, so
$v(RC_{gj}^2)\ge2v_p(a)+2e-2e(k_j-1)\ge2v_p(a)-46e>v_p(12)$ for $k_j\in\{1,25\}$. Each factor
$1+RC_{gj}^2$, hence each $W_g$ and $W_g^{-1}$, is $\equiv1$ to valuation $>v_p(12)$ at every
place above $p$, so $\Theta-12=\operatorname{Tr}\sum_g(W_g^{-1}-1)$ has valuation $>v_p(12)$ and
$v_p(\Theta)=v_p(12)$. Finally $v_p(B)=v(R)-2v_p(12)\ge2v_p(a)-2v_p(12)\ge4$. This is the
manuscript's real-place argument ($a\to0$) transported to $\mathbb Q_p$.

## Depends on

- [The slope predicate](../multiplication/certificate/slope-predicate.md)

## Proof depends on

- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](../multiplication/local/primes-above-p.md)

## Sources

- [Lemma P](../../sources/route-ap-locators.md#lemma-p)
