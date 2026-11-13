---
article_id: af_cee2912803350d1b4d415293
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Mult.pole_input_valuations, ZInQ.Mult.poleInput
---

# Valuations of the pole input of a completed slope

Let $t\in\mathbb Q$ satisfy conditions 1-4 of the slope representation (for some
$B_0$), and let $P(t)$ be its set of odd contact primes outside $S_b$. Let
$\eta\in\{1,-1\}$, $R_0=\eta F(t)/(t-1)^8$, and let $q\in\mathbb Q$ satisfy $v_p(q)\ge C_p$ for
$p\in S_b$ and $v_p(q)\ge0$ for $p\in P(t)$, with $a=1-R_0q^2\ne0$; put $R=\ell_0^2a^2R_0$. Let
$D_{gj}\in K_0$ ($1\le g\le6$, $1\le j\le12$) satisfy

- (i) $v_{\mathfrak p}(D_{gj})\ge0$ for all $g,j$ and every prime $\mathfrak p$ above a prime of
  $S_b$;
- (ii) for each $p\in P(t)$ there are $g$ and a prime $\mathfrak p$ above $p$ with
  $v_{\mathfrak p}(D_{gj})\ge k_j$ for all $j$;

and form $C_{gj},W_g,\Theta$ as in the slope predicate, assuming $W_g\ne0$ and $\Theta\ne0$.
Then $B=R/\Theta^2$ satisfies:

1. $v_p(B)\ge103C_p+8\ge4$ for every $p\in S_b$, in particular for every $p\in S_0$;
2. $v_p(B)=1$ for every $p\in P(t)$;
3. $v_p(B)$ is even for every other prime $p\notin S_b$.

Consequently the reduced denominator of $B$ is a perfect square.

**Proof sketch.** (1) Let $p\in S_b$. By condition 2, $|v_p(R_0)|\le C_p$ and
$|v_p(t-1)|\le C_p$, so $v_p(R_0q^2)\ge C_p>0$ and $a$ is a $p$-adic unit; with
$v_p(\ell_0)=E_p$, $v_p(R)=2E_p+v_p(R_0)$. Measuring valuations above $p$ on the scale of
$v_p$, (i) gives $v(C_{gj})\ge-25C_p-26C_p=-D_p$, so
$v(RC_{gj}^2)\ge2E_p-C_p-2D_p>v_p(12)$ by the clearing inequalities. Hence $W_g^{-1}-1$ has
valuation $>v_p(12)$ at every place above $p$, and so does
$\Theta-12=\operatorname{Tr}\sum_g(W_g^{-1}-1)$; thus $v_p(\Theta)=v_p(12)$ and
$v_p(B)=2E_p+v_p(R_0)-2v_p(12)\ge2E_p-C_p-2v_p(12)=103C_p+8$. (2) Let $p\in P(t)$. By
condition 3 and the contact valuations, $v_p(R_0)=1$ and $v_p(t-1)=0$; $v_p(q)\ge0$ makes $a$
a unit, and $v_p(\ell_0)=0$, so $v_p(R)=1$. At each place $\mathfrak q$ above $p$,
$v_{\mathfrak q}(1+RC^2)=\min(0,1+2v_{\mathfrak q}(C))$, so $W_g^{-1}$ is $\mathfrak q$-integral
with residue $1$ if all $v_{\mathfrak q}(C_{gj})\ge0$ and residue $0$ otherwise. Fix a place
$\mathfrak p$ above $p$; the twelve summands $W_g^{-1},\sigma(W_g^{-1})$ of $\Theta$ are then
$\mathfrak p$-integral with residues $0$ or $1$ (the residue of $\sigma(W_g^{-1})$ at $\mathfrak p$
being that of $W_g^{-1}$ at $\sigma\mathfrak p$), and by (ii) the assigned group and place, where
all $v(C_{gj})=v(D_{gj})-k_j\ge0$, contributes residue $1$. The sum of the residues
lies in $\{1,\dots,12\}$ and $p>324$, so $v_p(\Theta)=0$ and $v_p(B)=1$. (3) For $p\notin S_b$,
$p\notin P(t)$: if $v_p(t)<0$ then $v_p(R_0)=6v_p(t)-8v_p(t)$ is even; otherwise at most one of
the seven values $t-c$, $t-1$ has positive valuation, and that valuation is even (for $t-c$)
or enters multiplied by $8$ (for $t-1$). So $v_p(R_0)$ is even, $v_p(R)=2v_p(\ell_0a)+v_p(R_0)$
is even, and so is $v_p(B)=v_p(R)-2v_p(\Theta)$. Every negative valuation of $B$ is therefore
even.

## Depends on

- [The slope predicate](../certificate/slope-predicate.md)
- [The slope representation](slope-representation.md)
- [Prime sets and clearing exponents of the multiplication certificate](../certificate/constants.md)

## Proof depends on

- [Properties of the multiplication constants](../certificate/constants-properties.md)
- [The clearing inequalities](../certificate/clearing-arithmetic.md)
- [Valuations of the normalization at an odd contact prime](../soundness/contact-valuations.md)
- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](../local/primes-above-p.md)
- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../../model/field/special-primes.md)

## Sources

- [Pole input of a completed slope](../../../sources/multiplication-locators.md#pole-input-of-a-completed-slope)
- [Fixed local clearing](../../../sources/multiplication-locators.md#fixed-local-clearing)
