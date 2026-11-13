---
article_id: af_df88386e87dd78513b1a2952
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.JHeight.heightX, ZInQ.JHeight.JHeightBound
---

# The $j$-form of the height hypothesis

Let $\mathcal C$, $D$, $E_0$, $Q_R=R^{RE_0}$ and $C_{\rm cm}$ be as in the six-contact height
estimate, for a reduced fraction $a/b$ with $b>0$ let $h(a/b)=\log\max(|a|,b)$, and let $J$ be the
Hauptmodul value. For real $R$ put
$$X(R)=\max\bigl(1,C_{\rm cm},Q_R^{17}\bigr).$$
For a finite set $S$ of natural numbers and $u\in\mathbb Q\setminus\mathcal C$, $M_S(u)$ is the
product of the primes $p\notin S$ for which $v_p(u-c)$ is positive and odd for some
$c\in\mathcal C$ (as in the six-contact estimate, now for any such $S$).

For a finite set $S$ of natural numbers, the $j$-form of the height hypothesis at $S$ is the
assertion that for every $u\in\mathbb Q\setminus\mathcal C$,
$$h(J(u))\le(40\cdot10^4\cdot2^{24}+22)\,X(D)\,M_S(u)^{24}.$$

The main theorems use it at $S=S_{\rm mul}$.

The constant comes from combining three bounds of the manuscript's proof of the six-contact
estimate, for $j=J(u)$, the projective height $h([z_m])$ of the even theta constants of an abelian
surface $A$ and its Faltings height $h_F(A)$: $h(j)\le40h([z_m])+22$,
$h([z_m])\le10^4\cdot2^{24}\max(1,h_F(A))$ and $\max(1,h_F(A))\le X(R)\,M_S(u)^{24}$, using
$\max(1,h_F(A))\ge1$; the $j$-form takes this at $R=D$. The manuscript does not display the
combination. It proves the bound on $\max(1,h_F(A))$ only for $S$ containing every prime at most
$324$ and $R\ge\max(D,\max S,10^{12})$. So the combination gives the $j$-form at $R=D$ only for
such $S$ with $\max S\le D$, among them $S=S_{\rm mul}$
([every prime of $S_{\rm mul}$ is at most $D$](../six-contact-min-of-estimate.md)), the only set
the main theorems use.

The $j$-form is not a published theorem; it rests on the steps of the trust statement for H before
the last one, some of which replace or re-source the manuscript's steps and some of which no
referee has checked. At $S=S_{\rm mul}$ it implies the minimal height hypothesis
([proved here](six-contact-min-of-j-height-bound.md)). Here it is a hypothesis of two variants of
the main theorem
([the main theorem from the $j$-form and the L-series statements](../main-theorem-literature.md)).

## Depends on

- [The Hauptmodul value $J(u)$](hauptmodul-value.md)
- [The six-contact height estimate](../six-contact-estimate.md)

## Sources

- [The $j$-form of H](../../../sources/height-locators.md#the-j-form-of-h)
- [The trust statement for H](../../../sources/height-locators.md#the-trust-statement-for-h)
