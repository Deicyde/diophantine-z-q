---
article_id: af_939d2c81953715260cde59e4
declaration: theorem
origin: background
---

# The formal group of $y^2=x^3+Ax$

Let $K$ be a field of characteristic $0$, complete with respect to a discrete valuation $v$
normalized by $v(K^\times)=\mathbb Z$, with valuation ring $\mathcal O$, maximal ideal
$\mathfrak m$ and residue characteristic $p>0$. Let $A\in\mathcal O$, $A\ne0$, and
$W:y^2=x^3+Ax$ over $K$. Put
$$W_1(K)=\{O\}\cup\{(x,y)\in W(K):v(x)<0\},$$
and for $P=(x,y)\in W_1(K)$ put $z(P)=-x/y$ and $w(P)=1/x$, with $z(O)=w(O)=0$. Then:

1. for every affine $P=(x,y)\in W_1(K)$ there is an integer $N\ge1$ with $v(x)=-2N$ and
   $v(y)=-3N$; hence $z(P)$ is defined, $v(z(P))=N$ and $v(w(P))=2N=2v(z(P))$;
2. there is a commutative formal group law $F(T_1,T_2)=T_1+T_2+(\text{higher terms})$ in
   $\mathcal O[[T_1,T_2]]$ such that $z(P+Q)=F(z(P),z(Q))$ for all $P,Q\in W_1(K)$ (the series
   converges because $z(P),z(Q)\in\mathfrak m$); in particular $W_1(K)$ is a subgroup of
   $W(K)$ and $z:W_1(K)\to\mathfrak m$ is injective;
3. for every integer $k\ge1$, $W_k(K)=\{P\in W_1(K):v(z(P))\ge k\}$ (with $O\in W_k(K)$) is a
   subgroup;
4. for every $P\in W_1(K)$ and $n\in\mathbb Z$, $v(z([n]P))\ge v(z(P))$.

In part 1, $w=1/x$ is the manuscript's parameter; it differs from the auxiliary variable
$-1/y$ of Silverman.

**Proof sketch.** (1) If $v(x)<0$ then $v(Ax)\ge v(x)>3v(x)$, so $2v(y)=v(x^3+Ax)=3v(x)$;
thus $v(x)$ is even, $v(x)=-2N$, $v(y)=-3N$. (2) This is Silverman IV.1-IV.2 and VII.2.2:
with $\tilde w=-1/y$, the curve becomes $\tilde w=z^3+Az\tilde w^2$, which has a unique solution
$\tilde w(z)=z^3(1+\cdots)\in\mathcal O[[z]]$ (Silverman IV.1.1); the chord through two points
of the formal neighbourhood yields $F\in\mathcal O[[T_1,T_2]]$ (Silverman IV.1.2), and for points
with $v(x)<0$ the identity $\tilde w(P)=\tilde w(z(P))$ holds by Hensel's lemma, so the
geometric sum corresponds to $F$. Silverman states VII.2.2 for a minimal equation, but the
proof uses only that the coefficients lie in $\mathcal O$. (3) If $v(T_1),v(T_2)\ge k$ then
$v(F(T_1,T_2))\ge k$, and the formal inverse $i(T)\in T\mathcal O[[T]]$ preserves valuations.
(4) $[n]_F(T)\in T\mathcal O[[T]]$ for every $n\in\mathbb Z$, by induction from
$[n+1]_F(T)=F([n]_F(T),T)$ and $[-1]_F=i$.

## Depends on

None.

## Sources

- [Local conventions](../../../sources/multiplication-locators.md#local-conventions)
- [Silverman](../../../sources/multiplication-locators.md#silverman)
