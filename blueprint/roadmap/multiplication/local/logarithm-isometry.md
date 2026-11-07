---
article_id: af_e49ffcac35f49630c3c40135
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Mult.evalLog_isometry, ZInQ.Mult.ellLog_injOn, ZInQ.Mult.val_z_zsmul_eq
---

# The isometry range of the formal logarithm

In the setting of the formal logarithm of $W:y^2=x^3+Ax$ over $K$, with residue
characteristic $p$ and $e=v(p)$:

1. if $t\in K$ and $v(t)>e/(p-1)$, then $v(\log(t)-t)>v(t)$, so $v(\log(t))=v(t)$;
2. consequently, on the subgroup of $P\in W_1(K)$ with $v(z(P))>e/(p-1)$ (together with $O$),
   $\lambda$ is injective, $v(\lambda(P))=v(z(P))$, and for $n\in\mathbb Z\setminus\{0\}$,
   $$v\bigl(z([n]P)\bigr)=v\bigl(z(P)\bigr)+v(n).$$

In particular, if $p$ is odd and $e=1$, then $e/(p-1)<1$, so (2) holds on all of $W_1(K)$:
$W_1(K)$ is torsion-free and $\lambda$ is injective on it.

This is the manuscript's statement that the logarithm "is an isometry with inverse exponential
on $v(z)>e/(p-1)$" (Silverman IV.6.3-IV.6.4), with its reason: the degree-$r$ coefficient has
denominator dividing $r$, so each relative error has valuation at least
$(r-1)v(z)-e\,v_p(r)>0$.

**Proof sketch.** (1) For $r\ge2$ the term $b_{r-1}t^r/r$ has valuation relative to $t$ at
least $(r-1)v(t)-e\,v_p(r)$. Since $p^{v_p(r)}\le r$ and $p^m\ge1+m(p-1)$, one has
$v_p(r)\le(r-1)/(p-1)$, so this is at least $(r-1)\bigl(v(t)-e/(p-1)\bigr)>0$; the relative
errors also tend to infinity with $r$, so the tail $\log(t)-t$ has valuation $>v(t)$. (2) Let
$k$ be the least integer $>e/(p-1)$; by the filtration, $W_k(K)$ is a subgroup and the set in
question. For $P\in W_k(K)\setminus\{O\}$, (1) gives $v(\lambda(P))=v(z(P))<\infty$, so
$\lambda(P)\ne0$; as $\lambda$ is a homomorphism, it is injective on $W_k(K)$. For $n\ne0$,
$[n]P\in W_k(K)$, $[n]P\ne O$ by injectivity ($\lambda([n]P)=n\lambda(P)\ne0$), and
$v(z([n]P))=v(\lambda([n]P))=v(n\lambda(P))=v(n)+v(z(P))$.

## Depends on

- [The formal logarithm](formal-logarithm.md)
- [The formal neighbourhood of $y^2=x^3+Ax$ and its filtration](formal-group.md)

## Sources

- [Local conventions](../../../sources/multiplication-locators.md#local-conventions)
- [Silverman](../../../sources/multiplication-locators.md#silverman)
