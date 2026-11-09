---
article_id: af_5cc5a7d088841f393cccbc20
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Mult.finite_box
---

# The finite-box deduction

Assume the minimal height hypothesis. Let
$n_1,n_2,n_3\in\mathbb Z$ with $n_1n_2\ne n_3$, and suppose the unguarded certificate accepts
$(\iota(n_1),\iota(n_2),\iota(n_3))$:
$$\mathrm{Rel}_{\mathtt{height\_certificate}}\bigl(\iota(n_1),\iota(n_2),\iota(n_3),\ell_0,\iota(c_*),\iota(c_*n_1),\iota(c_*n_2),\iota(c_*n_3)\bigr).$$
Then
$$\max_i|n_i|<T=(48A_{\rm ht})^{13}.$$

This is Proposition 6.1, with the height estimate applied to $S_{\rm mul}$ in its minimal form
and its constant $H_6(D)$ weakened to $A_{\rm ht}$. The bound is symbolic: neither $A_{\rm ht}$ nor $T$ is evaluated.

**Proof sketch.** Put $f=n_1n_2-n_3\ne0$ and $N=\max_i|n_i|$; then $N\ge1$ and
$|f|\le N^2+N\le2N^2$. By the height-certificate semantics there are $a_{ij},b_i$ and $27$
slopes $t$, each with $\mathrm{Slope}(t,\ell_0;c_*,c_*n_1,c_*n_2,c_*n_3)$, such that each of the
nine quantities is a sum of three slopes. Each slope has $h(t)\le A_{\rm ht}|f|^{24/25}$. The
sum and quotient bounds give $h(a_{ij}),h(b_i)\le3A_{\rm ht}|f|^{24/25}+\log3$ and, for the
rational components $x_{ij}=a_{ij}/b_i$ of $x([n_i]P_0)$,
$h(x_{ij})\le6A_{\rm ht}|f|^{24/25}+2\log3$. The height bounds in $K_0$ give, for $n_i\ne0$,
$$h\bigl(\epsilon^4x([n_i]P_0)\bigr)\le12A_{\rm ht}|f|^{24/25}+4\log3+\tfrac32\log2+2\log(1+\sqrt2),$$
and the canonical height of multiples of $P_0$ yields
$$2n_i^2\,\widehat h(P_0)\le12A_{\rm ht}|f|^{24/25}+B_0,$$
trivially also for $n_i=0$. As $2\widehat h(P_0)>1$ and $B_0<10$, for the index with $|n_i|=N$:
$N^2\le12A_{\rm ht}(2N^2)^{24/25}+B_0<24A_{\rm ht}N^{48/25}+10$. Since $A_{\rm ht}\ge1$, the final
inequality gives $N<(48A_{\rm ht})^{13}=T$.

## Depends on

- [The height certificate template](../../syntax/templates/template-height-certificate.md)
- [Prime sets and clearing exponents of the multiplication certificate](../certificate/constants.md)
- [Point codes](../../model/point-codes.md)
- [The minimal height hypothesis](../../main/six-contact-min.md)

## Proof depends on

- [Semantics of the height certificate template](../certificate/height-certificate-semantics.md)
- [The height of an accepted slope](contact-support.md)
- [Sum and quotient bounds for rational heights](rational-height-bounds.md)
- [Height bounds in $K_0$](field-height-bounds.md)
- [The canonical height of multiples of $P_0$](generator-height.md)
- [Explicit height constants](height-constants.md)
- [The final inequality of the finite-box deduction](box-inequality.md)
- [Properties of the multiplication constants](../certificate/constants-properties.md)

## Sources

- [Finite-box deduction](../../../sources/multiplication-locators.md#finite-box-deduction)
