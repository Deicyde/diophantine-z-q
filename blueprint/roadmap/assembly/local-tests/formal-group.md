---
article_id: af_6c4778df56f0b27cf759ca28
declaration: lemma
origin: background
---

# Formal neighbourhoods of the identity

Let $\pi$ be a prime element of $\mathbb Z[s]$ and $v=v_\pi$. For an integer $k\ge1$ let
$$E_k(\pi)=\{O\}\cup\{(x,y)\in E(K_0):\ v(x)\le-2k\}.$$
Then:

1. every affine $P=(x,y)\in E(K_0)$ with $v(x)<0$ has $v(x)=-2K$, $v(y)=-3K$, $v(z(P))=K$ and
   $v(w(P))=2K$ for an integer $K\ge1$; write $\nu_\pi(P)=K$, and $\nu_\pi(O)=\infty$;
2. each $E_k(\pi)$ is a subgroup of $E(K_0)$, and $E_1(\pi)\supseteq E_2(\pi)\supseteq\cdots$;
3. for $P,Q\in E_k(\pi)$, with $z(O)=0$,
   $$v\bigl(z(P+Q)-z(P)-z(Q)\bigr)\ge5k,\qquad z(-P)=-z(P).$$

This holds at every prime $\pi$, including $s$ and $d$, because the coefficient $A=-d^2$ of
$E:y^2=x^3+Ax$ is integral everywhere.

**Proof sketch.** (1) If $v(x)<0$ then $v(x^3)=3v(x)<v(A)+v(x)$, so $2v(y)=3v(x)$; hence
$v(x)=-2K$, $v(y)=-3K$.

(2), (3) Use the coordinates $z=-x/y$, $\omega=-1/y$ near $O$, in which the curve is
$\omega=z^3+Az\omega^2$ and $(x,y)=(z/\omega,-1/\omega)$; on $E_k(\pi)$, $v(z)\ge k$ and $v(\omega)=3v(z)\ge3k$,
and $-P$ has coordinates $(-z,-\omega)$. Let $P_1,P_2\in E_k(\pi)$ be affine with $P_2\ne-P_1$ (the
cases with $O$ or $P_2=-P_1$ are immediate). From the curve equation,
$$(\omega_2-\omega_1)\bigl(1-Az_1(\omega_1+\omega_2)\bigr)=(z_2-z_1)\bigl(z_1^2+z_1z_2+z_2^2+A\omega_2^2\bigr),$$
so the line through $P_1,P_2$ (the tangent if $P_1=P_2$) is $\omega=\mu z+\nu$ with
$\mu=(z_1^2+z_1z_2+z_2^2+A\omega_2^2)/(1-Az_1(\omega_1+\omega_2))$, $v(\mu)\ge2k$, and $\nu=\omega_1-\mu z_1$,
$v(\nu)\ge3k$. Substituting into the curve gives the cubic
$(1+A\mu^2)z^3+2A\mu\nu z^2+(A\nu^2-\mu)z-\nu=0$ with roots $z_1,z_2,z_3$, where $z_3$ is the third
intersection $-(P_1+P_2)$. Hence
$$z(P_1+P_2)=-z_3=z_1+z_2+\frac{2A\mu\nu}{1+A\mu^2},$$
with $v\bigl(2A\mu\nu/(1+A\mu^2)\bigr)\ge5k$, so $v(z(P_1+P_2))\ge k$; and $\omega_3=\mu z_3+\nu$ has
$v(\omega_3)\ge3k>0$, so $P_1+P_2$ is $O$ or affine with $v(y)<0$, hence $v(x)<0$, and then by (1)
$v(x)=-2v(z)\le-2k$. This is the formal group law of the integral Weierstrass equation
(Silverman IV.1 and VII.2.2), without power series.

## Depends on

- [The generator curve $E$](../../model/field/generator-curve.md)
- [The precision quantities and the precision predicate](../approximation/precision-predicate.md)

## Proof depends on

- [Valuations of the quadratic field](k0-valuations.md)

## Sources

- [Section 6 formal conventions](../../../sources/assembly-locators.md#section-6-formal-conventions)
- [Lemma 11.1](../../../sources/assembly-locators.md#lemma-111)
- [Silverman](../../../sources/assembly-locators.md#silverman)
