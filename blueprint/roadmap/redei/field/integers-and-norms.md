---
article_id: af_554cdaa7ab0b215c3420ae52
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.normZ_eq_mul_conj, ZInQ.RouteK.Redei.isIntegral_omega, ZInQ.RouteK.Redei.omegaO, ZInQ.RouteK.Redei.algebraMap_omegaO, ZInQ.RouteK.Redei.coe_omegaO, ZInQ.RouteK.Redei.omegaO_sq, ZInQ.RouteK.Redei.conj_omegaO, ZInQ.RouteK.Redei.theta_eq, ZInQ.RouteK.Redei.isIntegral_theta, ZInQ.RouteK.Redei.thetaO, ZInQ.RouteK.Redei.algebraMap_thetaO, ZInQ.RouteK.Redei.two_mul_thetaO, ZInQ.RouteK.Redei.algNorm_eq, ZInQ.RouteK.Redei.norm_eq_mul_conj, ZInQ.RouteK.Redei.norm_nonneg, ZInQ.RouteK.Redei.algNorm_coe, ZInQ.RouteK.Redei.normZ_nonneg, ZInQ.RouteK.Redei.finrank_int, ZInQ.RouteK.Redei.normZ_intCast, ZInQ.RouteK.Redei.normZ_natCast, ZInQ.RouteK.Redei.normZ_omega, ZInQ.RouteK.Redei.normZ_one_add_omega
---

# Integers and norms of $\mathbb Q(\sqrt{-n})$

Let $n\ge1$, $K=\mathbb Q(\omega)$ with $\omega^2=-n$, $\mathcal O$ its ring of integers and
$\sigma$ its nontrivial automorphism.

- $\omega$ lies in $\mathcal O$, with $\omega^2=-n$ and $\sigma(\omega)=-\omega$ there. Put
  $\theta=(1+\omega)/2=\tfrac12+\tfrac12\omega$. If $n\equiv3\pmod4$, then $\theta$ lies in
  $\mathcal O$, and $2\theta=1+\omega$.
- The norm of $K/\mathbb Q$ is $N(a+b\omega)=a^2+nb^2$. For every $x\in K$, $N(x)=x\,\sigma(x)$
  and $N(x)\ge0$.
- $\mathcal O$ has rank $2$ over $\mathbb Z$. For $x\in\mathcal O$, the norm $N(x)$ is an integer,
  the norm of $x$ over $\mathbb Z$; it satisfies $N(x)\ge0$ and $N(x)=x\,\sigma(x)$ in $\mathcal O$.
  Moreover $N(m)=m^2$ for $m\in\mathbb Z$, $N(\omega)=n$ and $N(1+\omega)=1+n$.

**Proof sketch.** $\omega$ is a root of $X^2+n$, and $\sigma(\omega)=-\omega$ in $\mathcal O$
because it holds in $K$. For $n+1=4m$, $\theta$ is a root of $X^2-X+m$. The norm is the
determinant of multiplication by $x=a+b\omega$ on the basis $1,\omega$, which is $a^2+nb^2\ge0$. It
equals $(a+b\omega)(a-b\omega)=x\,\sigma(x)$ because $\sigma$ is the conjugation. For $x\in\mathcal O$ the norm of $K/\mathbb Q$ is the norm of
$\mathcal O/\mathbb Z$, so it is an integer; since $\mathcal O$ has rank $[K:\mathbb Q]=2$ over
$\mathbb Z$, $N(m)=m^2$. The values $N(\omega)=n$ and $N(1+\omega)=1+n$ are the formula
$a^2+nb^2$.

## Depends on

- [The conjugation of $\mathbb Q(\sqrt{-n})$](conjugation.md)

## Sources

- [Step 1: the field](../../../sources/redei-locators.md#step-1-the-field)
