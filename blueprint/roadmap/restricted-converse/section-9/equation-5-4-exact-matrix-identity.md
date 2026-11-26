---
article_id: af_85cd0ab087e0cec7e3b66031
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Uniform.exactChebotarevRealizationGenuine_of_localization, ZInQ.Manuscript.RC.Uniform.ExactChebotarevRealizationGenuine
---

# (5.4): the exact matrix identity at a new prime

Assume that localization at a new prime is evaluation at the square of its Frobenius, to the retained
precision (`NewPrimeLocalization`, ELLIOT): at each stage $i$, for every prime $\ell$ outside the primes
already used, unramified in the stage compositum and inert in $K$, and every Frobenius $\mathrm{Fr}$ at
$\ell$, the localization matrix of the basis cochains at $\ell$ agrees with their evaluation at
$\mathrm{Fr}^2$ modulo $(2^{n(i)},t^{n(i)})$.

Let $\mathcal U$ be a nonprincipal ultrafilter on the coefficient stages, $n(i)\to\infty$ the retained
precisions, $M_i$ finite Galois stage composita containing $K=\mathbb Q(\sqrt k)$ with $k<0$, $\tau$ a
complex conjugation and $h_i$ automorphisms trivial on $K$. Then at every stage there are a new prime
$\ell_i$, unramified in $M_i$ and inert in $K$, and a Frobenius $\mathrm{Fr}_i$ at $\ell_i$ with
$\mathrm{Fr}_i|_{M_i}=\tau h_i|_{M_i}$, such that the inner limits satisfy exactly
$$L=E_{\sigma^2},\qquad\sigma=\tau h,\tag{5.4}$$
where $L$ is the limit of the localization matrices at the new primes and $E_{\sigma^2}$ the limit of the
evaluation matrices at $(\tau h_i)^2$.

The manuscript states (5.4) for each instance of a sequence; the Lean theorem treats one instance, and
`exactChebotarevRealizationGenuine_family` applies it to all of them with one ultrafilter. Selmer
complexes over $\Lambda$ and their localization maps are not in Lean, so the localization matrices are
abstract and their link to evaluation is the input.

The reduction of Theorem 5.3 does not use this theorem: the switch steps that it serves in
[Proposition 9.6](proposition-9-6-uniform-lower-bound.md) are part of the fields `PreLeaves.eq35` and
`PostLeaves.prim_regular` of [the remaining hypotheses](../remaining-hypotheses.md).

**Proof sketch.** The repository's Chebotarev theorem gives at each stage a new prime with a Frobenius
restricting to $\tau h_i$; the prime is inert in $K$ because $\tau$ moves $\sqrt k$ and $h_i$
fixes it. The input makes the stage matrices agree modulo the stage ideals, and the inner ultralimit
turns these congruences into an exact identity over $\Lambda$.

## Depends on

None.

## Sources

- [Section 9](../../../sources/manuscript.md#section-9)
