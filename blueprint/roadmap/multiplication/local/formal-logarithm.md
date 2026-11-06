---
article_id: af_6232cd6ae4ba063700a677b4
declaration: theorem
origin: background
---

# The formal logarithm and its isometry range

In the setting of the formal group of $W:y^2=x^3+Ax$ over the complete field $K$, put
$e=v(p)\ge1$. There is a power series
$$\log(T)=\sum_{r\ge1}\frac{b_{r-1}}{r}\,T^r\in K[[T]],\qquad b_i\in\mathcal O,\ b_0=1,$$
such that:

1. $\log(F(T_1,T_2))=\log(T_1)+\log(T_2)$ in $K[[T_1,T_2]]$, and $\frac{d}{dT}\log(T)\,dT$ is the
   expansion in $z$ of the invariant differential $dx/(2y)$;
2. for $t\in K$ with $v(t)>0$ the series $\log(t)$ converges, and
   $\lambda(P)=\log(z(P))$ defines a group homomorphism $\lambda:W_1(K)\to(K,+)$;
3. if $v(t)>e/(p-1)$, then $v(\log(t)-t)>v(t)$, so $v(\log(t))=v(t)$;
4. consequently, on the subgroup of $P\in W_1(K)$ with $v(z(P))>e/(p-1)$ (together with $O$),
   $\lambda$ is injective, $v(\lambda(P))=v(z(P))$, and for $n\in\mathbb Z\setminus\{0\}$,
   $\lambda([n]P)=n\lambda(P)$ and $v(z([n]P))=v(z(P))+v(n)$.

In particular, if $p$ is odd and $e=1$, then $e/(p-1)<1$, so part 4 holds on all of
$W_1(K)$: $W_1(K)$ is torsion-free and $\lambda$ is injective on it.

**Proof sketch.** (1)-(2) are Silverman IV.4.2, IV.5.2 and IV.5.5: the normalized invariant
differential of $F$ is $\omega(T)\,dT$ with $\omega\in\mathcal O[[T]]$, $\omega(0)=1$; its formal
integral is $\log$, whose degree-$r$ coefficient is $b_{r-1}/r$; invariance of $\omega$ gives
$\log\circ F=\log+\log$, and convergence for $v(t)>0$ follows from
$v(b_{r-1}t^r/r)\ge rv(t)-e\log_p r\to\infty$ (Silverman IV.6.3). (3) is the manuscript's
estimate: for $r\ge2$ the term $b_{r-1}t^r/r$ has valuation relative to $t$ at least
$(r-1)v(t)-e\,v_p(r)$, which is positive because $v_p(r)\le(r-1)/(p-1)$; this is Silverman
IV.6.4. (4) follows from (2), (3) and the subgroup property of the filtration; for
$n\ne0$, $v(z([n]P))=v(\lambda([n]P))=v(n\lambda(P))=v(n)+v(z(P))$.

## Depends on

- [The formal group of $y^2=x^3+Ax$](formal-group.md)

## Sources

- [Local conventions](../../../sources/multiplication-locators.md#local-conventions)
- [Silverman](../../../sources/multiplication-locators.md#silverman)
