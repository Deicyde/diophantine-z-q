---
article_id: af_fdd11da248e86a22d5f24b93
declaration: lemma
origin: background
---

# Multiplication in a formal neighbourhood

Let $\pi$ be a prime element of $\mathbb Z[s]$ above the rational prime $p$, $v=v_\pi$, and let
$Q\in E(K_0)$ be affine with $K=\nu_\pi(Q)\ge1$ (that is, $v(x(Q))=-2K<0$). Then:

1. for every $n\in\mathbb Z$, $v\bigl(z([n]Q)-n\,z(Q)\bigr)\ge5K$, hence
   $v\bigl(z([n]Q)/z(Q)-n\bigr)\ge4K$;
2. $[p]Q\in E_{K+1}(\pi)$;
3. if $p$ is odd, then for every nonzero $m\in\mathbb Z$ the point $[m]Q$ is affine,
   $\nu_\pi([m]Q)=K+v_p(m)$, and
   $$z([m]Q)=m\,z(Q)\,u_m\qquad\text{with }v(u_m-1)\ge1 .$$

Item 3 is the content of "$\log([m]Q)=m\log(Q)$ and $\log$ is an isometry with
$\log(Q)=z(Q)(1+e_Q)$, $v(e_Q)\ge1$" used in the manuscript, in the form actually needed.

**Proof sketch.** (1) The multiples $[j]Q$ lie in the subgroup $E_K(\pi)$. By the formal group
estimate, $z([j+1]Q)=z([j]Q)+z(Q)+e_j$ with $v(e_j)\ge5K$; summing gives the claim for
$n\ge0$, and $z(-P)=-z(P)$ gives $n<0$. Divide by $z(Q)$, which has valuation $K$.

(2) By (1), $z([p]Q)=p\,z(Q)+e$ with $v(e)\ge5K$, and $v(p\,z(Q))=v(p)+K\ge K+1$; since
$5K\ge K+1$, $v(z([p]Q))\ge K+1$ (or $[p]Q=O$).

(3) Now $v(p)=1$. For $p\nmid m'$: by (1), $z([m']Q)=m'z(Q)(1+\epsilon)$ with
$v(\epsilon)\ge4K\ge1$, so $\nu_\pi([m']Q)=K$. For $p$: $z([p]Q)=p\,z(Q)(1+\epsilon)$ with
$v(\epsilon)\ge5K-(K+1)\ge3$, so $\nu_\pi([p]Q)=K+1$. Write $m=p^em'$ and compose, applying these
to $[p^i]Q$ (whose $\nu_\pi$ is $K+i$) and then to $[p^e]Q$; the units multiply and stay $\equiv1$.
In particular $z([m]Q)\ne0$, so $[m]Q\ne O$.

## Depends on

- [Formal neighbourhoods of the identity](formal-group.md)
- [Valuations of the quadratic field](k0-valuations.md)

## Sources

- [Section 6 formal conventions](../../../sources/assembly-locators.md#section-6-formal-conventions)
- [Lemma 11.1](../../../sources/assembly-locators.md#lemma-111)
- [Lemma 11.2](../../../sources/assembly-locators.md#lemma-112)
- [Silverman](../../../sources/assembly-locators.md#silverman)
