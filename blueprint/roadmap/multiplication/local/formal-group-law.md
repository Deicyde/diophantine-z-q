---
article_id: af_65f979c554aa55af4bc44249
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Mult.omegaSeries_hasSum, ZInQ.Mult.formalAdd, ZInQ.Mult.formalGroupLaw_exists, ZInQ.Mult.hasSum_formalAdd
---

# The formal group law of $y^2=x^3+Ax$

Let $K$ be a field of characteristic $0$, complete with respect to a discrete valuation $v$
normalized by $v(K^\times)=\mathbb Z$, with valuation ring $\mathcal O$ and maximal ideal
$\mathfrak m$. Let $A\in\mathcal O\setminus\{0\}$, $W:y^2=x^3+Ax$, and let $W_1(K)$ and $z$ be as
in the formal neighbourhood statement. Then:

1. there is a unique power series $\omega(T)\in\mathcal O[[T]]$ with
   $\omega(T)=T^3+AT\,\omega(T)^2$; it has the form $T^3(1+\cdots)$, and $\omega(P)=\omega(z(P))$
   (that is, $-1/y=\omega(-x/y)$) for every affine $P=(x,y)\in W_1(K)$;
2. there is a commutative formal group law $F(T_1,T_2)=T_1+T_2+(\text{terms of degree}\ge2)$ in
   $\mathcal O[[T_1,T_2]]$, with formal inverse $i(T)=-T$, such that
   $$z(P+Q)=F\bigl(z(P),z(Q)\bigr)\qquad(P,Q\in W_1(K)),$$
   the series converging because $z(P),z(Q)\in\mathfrak m$.

This is Silverman IV.1.1-IV.1.2 and VII.2.2; the manuscript uses it through the formal
logarithm.

**Proof sketch.** (1) The coefficients of $\omega$ are determined recursively by
$(*)$ $\omega=T^3+AT\omega^2$, since the coefficient of $T^n$ on the right involves only lower
coefficients of $\omega$; they lie in $\mathbb Z[A]\subset\mathcal O$ (Silverman IV.1.1). For an
affine $P\in W_1(K)$, both $\omega(P)$ and $\omega(z(P))$ are solutions $\omega_0$ of
$\omega_0=z^3+Az\omega_0^2$ with $v(\omega_0)\ge1$, where $z=z(P)$; the map
$\omega_0\mapsto z^3+Az\omega_0^2$ is a contraction of $\mathfrak m$ (its difference quotient
$Az(\omega_0+\omega_0')$ has positive valuation), so the solution is unique. (2) Replace the
elements $z_i,\omega_i$ in the chord construction of the formal neighbourhood statement by the
power series $T_i,\omega(T_i)$: the slope $\lambda(T_1,T_2)$, the intercept
$\nu=\omega(T_1)-\lambda T_1$ and
$$F(T_1,T_2)=T_1+T_2+\frac{2A\lambda\nu}{1+A\lambda^2}$$
are power series in $\mathcal O[[T_1,T_2]]$ (Silverman IV.1.2; the difference quotient defining
$\lambda$ is a polynomial expression in $T_1,T_2$ and the coefficients of $\omega$, and
$1+A\lambda^2$ is invertible). Evaluating at $(z(P),z(Q))$ and using (1) recovers
$-z_3=z(P+Q)$. The formal group law axioms for $F$ (associativity and commutativity as identities of power
series) are Silverman IV.1.2, deduced there from the group law of $W$; $i(T)=-T$ because negation is $z\mapsto-z$.

## Depends on

- [The formal neighbourhood of $y^2=x^3+Ax$ and its filtration](formal-group.md)

## Sources

- [Local conventions](../../../sources/multiplication-locators.md#local-conventions)
- [Silverman](../../../sources/multiplication-locators.md#silverman)
