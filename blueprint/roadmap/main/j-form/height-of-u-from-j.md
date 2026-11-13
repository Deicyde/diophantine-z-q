---
article_id: af_6ef94691c5342bf7662d953f
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.JHeight.twelve_mul_ratHeight_le
---

# From the height of $J(u)$ to the height of $u$

Let $\mathcal C$ be as in the six-contact height estimate, for a reduced fraction $a/b$ with $b>0$
let $h(a/b)=\log\max(|a|,b)$, and let $J$ be the Hauptmodul value.
For every $u\in\mathbb Q\setminus\mathcal C$,
$$12\,h(u)\le h(J(u))+450.$$

This replaces the manuscript's rational-root bound $h(u)<h(J(u))+74$, a different inequality.

**Proof sketch.** Write $u=a/b$ in lowest terms with $b>0$, and $F_h=F_h(a,b)$, $G_h=G_h(a,b)$.
Then $F(u)=F_h/b^6$ and $G(u)=G_h/b^2$, and $G_h>0$ since
$7G_h=(7a+150b)^2+2700b^2$. So $J(u)=n/d$ with $n=-57600F_h^2$ and $d=G_h^6>0$. Writing $J(u)$ in
lowest terms as $\nu/\delta$ with $\delta>0$, there is an integer $c$ with $n=c\nu$ and $d=c\delta$;
$c>0$ because $d,\delta>0$. Then $c$ divides both $57600F_h^2$ and $G_h^6$, so $c\mid C_0$ by the
cancellation bound, and $c\le C_0$. Hence
$$\max(57600F_h^2,\,G_h^6)=c\,H,\qquad H=\max(|\nu|,\delta)\ge1.$$
Put $m=\max(|a|,b)>0$. The lower bound gives
$$m^{12}\le10^{48}cH\le10^{48}C_0H\le10^{139}H.$$
Since $h(u)=\log m$ and $h(J(u))=\log H$, taking logarithms gives
$12h(u)\le139\log10+h(J(u))$. Finally $e>2.7$ and $2.7^3>10$ give $\log10<3$, so
$139\log10<417\le450$.

## Depends on

- [The Hauptmodul value $J(u)$](hauptmodul-value.md)
- [The six-contact height estimate](../six-contact-estimate.md)

## Proof depends on

- [The cancellation in $J(u)$ is bounded](cancellation-bound.md)
- [A lower bound for the larger of $57600F_h^2$ and $G_h^6$](lower-bound.md)

## Sources

- [Step F4](../../../sources/height-locators.md#step-f4)
