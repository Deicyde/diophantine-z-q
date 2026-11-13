---
article_id: af_f3f093451a60b041ccd99dff
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.conj_apply, ZInQ.RouteK.Redei.card_gal, ZInQ.RouteK.Redei.omega_sq, ZInQ.RouteK.Redei.conj_omega, ZInQ.RouteK.Redei.conj_unique, ZInQ.RouteK.Redei.conj_conj, ZInQ.RouteK.Redei.conj_mul_self, ZInQ.RouteK.Redei.eq_one_or_eq_conj, ZInQ.RouteK.Redei.exists_conj_ne_one, ZInQ.RouteK.Redei.algebraMap_smul
---

# The conjugation of $\mathbb Q(\sqrt{-n})$

Let $n\ge1$ and let $K=\mathbb Q(\omega)=\mathbb Q[\omega]/(\omega^2+n)$, so that $\omega^2=-n$.
Then $K$ has exactly two automorphisms over $\mathbb Q$, and a nontrivial one exists. Every
nontrivial automorphism $\sigma$ satisfies $\sigma(\omega)=-\omega$ and is the conjugation
$$\sigma(a+b\omega)=a-b\omega\qquad(a,b\in\mathbb Q).$$
Hence the nontrivial automorphism $\sigma$ is unique, $\sigma\circ\sigma=1$, and every
automorphism of $K$ is $1$ or $\sigma$. The automorphisms of $K$ act on its ring of integers
$\mathcal O$ compatibly with the inclusion $\mathcal O\subset K$.

**Proof sketch.** $K/\mathbb Q$ is Galois of degree $2$, so it has two automorphisms, and one of
them is not the identity. Let $\sigma\ne1$. The image $z=\sigma(\omega)$ is again a root of
$X^2+n$, so it has trace $0$ and norm $n$; writing $z=a+b\omega$, this gives $a=0$ and $b^2=1$.
If $b=1$, then $\sigma$ fixes the generator $\omega$, so $\sigma=1$. Hence $b=-1$, that is,
$\sigma(\omega)=-\omega$, and writing $x=a+b\omega$ gives $\sigma(x)=a-b\omega$. So any two
nontrivial automorphisms agree, and applying the conjugation twice gives the identity.

## Depends on

- [The genus class number](../genus-class-number.md)

## Sources

- [Step 1: the field](../../../sources/redei-locators.md#step-1-the-field)
