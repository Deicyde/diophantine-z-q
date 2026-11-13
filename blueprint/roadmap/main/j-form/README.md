---
article_id: af_ed2c7c4f0b22d1949d72c934
---

# The height hypothesis in its $j$-form

The proof of the six-contact estimate passes through the Hauptmodul value
$$J(u)=-57600\,\frac{F(u)^2}{G(u)^6},\qquad F(u)=u(u+15)(u+20)(u+24)(u+30)(u+60),\quad G(u)=7u^2+300u+3600.$$
For $j=J(u)$, the manuscript bounds $h(j)$ through the projective height $h([z_m])$ of the even
theta constants of an abelian surface $A$ and the Faltings height $h_F(A)$. Combining three of its
bounds, $h(j)\le40h([z_m])+22$,
$h([z_m])\le10^4\cdot2^{24}\max(1,h_F(A))$ and
$\max(1,h_F(A))\le\max(1,C_{\rm cm},Q_R^{17})M_S(u)^{24}$, gives, for $S$ and $R$ as in the
six-contact estimate,
$$h(J(u))\le(40\cdot10^4\cdot2^{24}+22)\max(1,C_{\rm cm},Q_R^{17})\,M_S(u)^{24}.$$
The manuscript does not display this combined bound; it returns from $J(u)$ to $u$ by the
rational-root theorem. This section proves the return as a different inequality,
$12h(u)\le h(J(u))+450$ for $u\notin\mathcal C$, from two explicit polynomial identities that bound
the cancellation in $J(u)$; it replaces the manuscript's rational-root step.

The $j$-form of the height hypothesis is the bound on $h(J(u))$ above at $R=D$, stated for every
$S$. It is not proved here and it is not a published theorem. It is what the argument of the
six-contact estimate gives before its last step, in the form of the trust statement for H: the
manuscript's steps, with the integral model and the CM case replaced, the finiteness of a twist
proved by an argument from another version of the manuscript, the theta expression for $j$ given
other published sources together with computations, and several steps checked by no
referee. That argument supports the
$j$-form at $S=S_{\rm mul}$, the set the main theorems use. At $S=S_{\rm mul}$ the $j$-form implies
the minimal height hypothesis
([the $j$-form implies the minimal height hypothesis](six-contact-min-of-j-height-bound.md)).

Notation ($\mathcal C$, $M_S$, $D$, $E_0$, $Q_R$, $C_{\rm cm}$) is as in
[the six-contact height estimate](../six-contact-estimate.md), and $h(a/b)=\log\max(|a|,b)$ for a
reduced fraction $a/b$ with $b>0$.

## The Hauptmodul value

- [The Hauptmodul value $J(u)$](hauptmodul-value.md)

## The $j$-form

- [The $j$-form of the height hypothesis](j-height-bound.md)

## Back from $J(u)$ to $u$

Two polynomial identities express $3a^7$ and $2^{10}3^85^6\,b^7$ as combinations of the binary
forms $F_h(a,b)$ and $G_h(a,b)$. They bound the common factor of the numerator and denominator of
$J(a/b)$, and they bound the larger of $57600F_h(a,b)^2$ and $G_h(a,b)^6$ below in terms of
$m=\max(|a|,|b|)$: $m^{12}\le10^{48}\max(57600F_h(a,b)^2,G_h(a,b)^6)$ when $m>0$. Together these
give the height of $u$ in terms of the height of $J(u)$.

- [The cancellation in $J(u)$ is bounded](cancellation-bound.md)
- [A lower bound for the larger of $57600F_h^2$ and $G_h^6$](lower-bound.md)
- [From the height of $J(u)$ to the height of $u$](height-of-u-from-j.md)

## The minimal height hypothesis from the $j$-form

- [The $j$-form implies the minimal height hypothesis](six-contact-min-of-j-height-bound.md)
