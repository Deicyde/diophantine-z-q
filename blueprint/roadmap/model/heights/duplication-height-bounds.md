---
article_id: af_46e2e02d9175f335f680763a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.hx_two_smul_bounds
---

# Height bounds for doubling on $C$

For every $T\in C(K_0)$,
$$4h_x(T)-\log392\ \le\ h_x([2]T)\ \le\ 4h_x(T)+\log676 .$$

**Proof sketch.** If $T=O$ both sides are trivial. If $T=(x,0)$, then $[2]T=O$ and
$x\in\{0,\pm\delta\}$ with $h(0)=0$ and $h(\pm\delta)=\tfrac12\log7$ (since
$\operatorname N(\delta)=7$ and both embeddings of $\delta$ exceed $1$); then
$4h_x(T)-\log392\le2\log7-\log392<0$ and the upper bound is trivial. Otherwise write
$x(T)=a/b$ with $a,b\in\mathbb Z[s]$ coprime, so
$h_x(T)=\frac12\sum_\sigma\log M_\sigma$ with $M_\sigma=\max(|\sigma a|,|\sigma b|)$. By the
duplication forms $x([2]T)=F_2(a,b)/G_2(a,b)$, and by the height of a fraction with
$g=\gcd(F_2,G_2)$,
$$h_x([2]T)=\tfrac12\Bigl(\sum_\sigma\log\max(|\sigma F_2|,|\sigma G_2|)-\log|\operatorname N(g)|\Bigr).$$
The archimedean bounds give $4\log M_\sigma\le\log\max(|\sigma F_2|,|\sigma G_2|)\le\log676+4\log M_\sigma$,
and $0\le\log|\operatorname N(g)|\le2\log392$ by the common-divisor lemma. Combining yields both
inequalities.

## Depends on

- [The $x$-height on $C(K_0)$](x-height.md)

## Proof depends on

- [The duplication forms on $C$](duplication-forms.md)
- [Archimedean bounds for the duplication forms](duplication-archimedean.md)
- [The common divisor of the duplication forms](duplication-common-divisor.md)
- [The height of a fraction in $\mathbb Z[\sqrt2]$](x-height-formula.md)
- [Explicit identities in $K_0$](../field/explicit-identities.md)

## Sources

- [Duplication bounds](../../../sources/model-locators.md#duplication-bounds)
