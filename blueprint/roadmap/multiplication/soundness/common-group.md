---
article_id: af_bf23c419353066e2df2a5d55
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.common_group
---

# The trace forces one common group and place

Let $t,\eta,q,R_0,a,R$ be as in the slope predicate with $\ell=\ell_0$ (so $t\notin\mathcal C\cup\{1\}$
and $a\ne0$), let $D_{gj}\in K_0$ ($1\le g\le6$, $1\le j\le12$) be arbitrary, and let
$C_{gj}$, $W_g$ and $\Theta$ be formed from them as in the slope predicate, with $W_g\ne0$,
$\Theta\ne0$ and $\Phi(R/\Theta^2)$. Let $p\notin S_b$ be an odd contact prime of $t$. Then
there are a group $g$ and a prime $\mathfrak p$ of $\mathbb Z[s]$ above $p$ such that
$$v_{\mathfrak p}(D_{gj})\ge1\quad(1\le j\le8),\qquad v_{\mathfrak p}(D_{gj})\ge25\quad(9\le j\le12).$$

The pole obstruction is used here, at the prime $p\notin S_0$; this is the only place where
the sound direction uses the pole predicate, and it does not use pole completeness.

**Proof sketch.** Let $k=v_p(t-c)$ and $r=v_p(R)$; by the contact valuations $k$ is odd,
$v_p(R_0)=k$, $v_p(t-1)=0$, and $r$ is odd with $r\le k$. Fix a prime $\mathfrak p_0$ above $p$
and let $\mathfrak q$ range over $\{\mathfrak p_0,\sigma\mathfrak p_0\}$. For each factor,
$v_{\mathfrak q}(RC_{gj}^2)=r+2v_{\mathfrak q}(C_{gj})$ is odd (or $C_{gj}=0$), hence
$v_{\mathfrak q}(1+RC_{gj}^2)=\min(0,r+2v_{\mathfrak q}(C_{gj}))$: no cancellation occurs. So
$v_{\mathfrak q}(W_g^{-1})=\sum_j\max(0,-r-2v_{\mathfrak q}(C_{gj}))\ge0$. Since
$\Theta=\sum_g(W_g^{-1}+\sigma W_g^{-1})$ and $v_{\mathfrak p_0}(\sigma y)=v_{\sigma\mathfrak p_0}(y)$,
$$v_p(\Theta)\ge m:=\min_{g,\mathfrak q}v_{\mathfrak q}(W_g^{-1})\ge0 .$$
The pole input $B=R/\Theta^2$ is nonzero with $\Phi(B)$, and $v_p(B)=r-2v_p(\Theta)$ is odd,
so by the pole obstruction it is positive: $v_p(\Theta)\le(r-1)/2$. In particular $r\ge1$ and
some pair $(g,\mathfrak q)$ has $s:=v_{\mathfrak q}(W_g^{-1})\le(r-1)/2$. For each $j$, either
$r+2v_{\mathfrak q}(C_{gj})>0$, so $v_{\mathfrak q}(C_{gj})\ge-(r-1)/2$, or the deficit
$-(r+2v_{\mathfrak q}(C_{gj}))$ is at most $s\le(r-1)/2$; in both cases
$v_{\mathfrak q}(C_{gj})\ge-(3r-1)/4$. Then
$v_{\mathfrak q}(D_{gj})=v_{\mathfrak q}(C_{gj})+k_jk\ge k_jk-(3k-1)/4$, which is $(k+1)/4>0$ for
$k_j=1$ and $(97k+1)/4\ge24.5$ for $k_j=25$; integrality gives the bounds $1$ and $25$. Take
$\mathfrak p=\mathfrak q$.

## Depends on

- [The slope predicate](../certificate/slope-predicate.md)
- [Prime sets and clearing exponents of the multiplication certificate](../certificate/constants.md)
- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](../local/primes-above-p.md)

## Proof depends on

- [Valuations of the normalization at an odd contact prime](contact-valuations.md)
- [The one-sided pole obstruction](../pole-obstruction.md)
- [Properties of the multiplication constants](../certificate/constants-properties.md)

## Sources

- [Local congruence](../../../sources/multiplication-locators.md#local-congruence)
