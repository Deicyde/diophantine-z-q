---
article_id: af_c62194024c502f07a89b3beb
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.JHeight.Fh, ZInQ.JHeight.Gh, ZInQ.JHeight.Jmap, ZInQ.JHeight.G_ne_zero
---

# The Hauptmodul value $J(u)$

For integers $a,b$ put
$$F_h(a,b)=a(a+15b)(a+20b)(a+24b)(a+30b)(a+60b),\qquad G_h(a,b)=7a^2+300ab+3600b^2,$$
a binary sextic and a binary quadratic form of discriminant $300^2-4\cdot7\cdot3600=-10800<0$.
For $u\in\mathbb Q$ the Hauptmodul value is
$$J(u)=-57600\,\frac{F(u)^2}{G(u)^6},\qquad F(u)=u(u+15)(u+20)(u+24)(u+30)(u+60),\quad G(u)=7u^2+300u+3600.$$

For every rational $u$, $G(u)\ne0$, since $7G(u)=(7u+150)^2+2700>0$; so the quotient defining
$J(u)$ never has a zero denominator.

## Depends on

None.

## Sources

- [The Hauptmodul value](../../../sources/height-locators.md#the-hauptmodul-value)
- [Step F4](../../../sources/height-locators.md#step-f4)
