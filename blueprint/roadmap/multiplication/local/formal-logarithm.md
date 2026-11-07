---
article_id: af_6232cd6ae4ba063700a677b4
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Mult.formalLog, ZInQ.Mult.ellLog, ZInQ.Mult.formalLog_formalAdd, ZInQ.Mult.ellLog_add, ZInQ.Mult.summable_log
---

# The formal logarithm

In the setting of the formal group law $F$ of $W:y^2=x^3+Ax$ over the complete field $K$, let
$p>0$ be the residue characteristic and $e=v(p)\ge1$. There is a power series
$$\log(T)=\sum_{r\ge1}\frac{b_{r-1}}{r}\,T^r\in K[[T]],\qquad b_i\in\mathcal O,\ b_0=1,$$
such that:

1. $\log(F(T_1,T_2))=\log(T_1)+\log(T_2)$ in $K[[T_1,T_2]]$, and $\frac{d}{dT}\log(T)\,dT$ is the
   expansion in $z$ of the invariant differential $dx/(2y)$;
2. for $t\in K$ with $v(t)>0$ the series $\log(t)$ converges, and
   $\lambda(P)=\log(z(P))$ defines a group homomorphism $\lambda:W_1(K)\to(K,+)$; in particular
   $\lambda([n]P)=n\lambda(P)$ for $P\in W_1(K)$ and $n\in\mathbb Z$.

This is the formal logarithm of Silverman IV.5; the manuscript states that it converges on
$v(z)>0$. Its isometry range is a separate statement.

**Proof sketch.** (1) is Silverman IV.4.2, IV.5.2 and IV.5.5: the normalized invariant
differential of $F$ is $\omega_F(T)\,dT$ with $\omega_F\in\mathcal O[[T]]$, $\omega_F(0)=1$; its
formal integral is $\log$, whose degree-$r$ coefficient is $b_{r-1}/r$; invariance of
$\omega_F$ under translation gives $\log\circ F=\log+\log$. The invariant differential of $W$
is $dx/(2y)$, and its expansion in $z$ is the invariant differential of $F$ (Silverman IV.1,
IV.5.1). (2) Convergence: $v(b_{r-1}t^r/r)\ge rv(t)-e\log_pr\to\infty$ (Silverman IV.6.3), and
in a complete nonarchimedean field a series whose terms tend to $0$ converges. Evaluating the
identity of (1) at $(z(P),z(Q))$ and using $z(P+Q)=F(z(P),z(Q))$ gives
$\lambda(P+Q)=\lambda(P)+\lambda(Q)$; evaluation of convergent power series in two variables
at elements of $\mathfrak m$ is a ring homomorphism.

## Depends on

- [The formal group law of $y^2=x^3+Ax$](formal-group-law.md)

## Sources

- [Local conventions](../../../sources/multiplication-locators.md#local-conventions)
- [Silverman](../../../sources/multiplication-locators.md#silverman)
