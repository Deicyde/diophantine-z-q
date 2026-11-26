---
article_id: af_c34c663c043a4442ece4196a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Rings.halfToFracO_mem_range_iff, ZInQ.Manuscript.RC.Rings.two_pow_mul_mem_lambda_of_mem_O, ZInQ.Manuscript.RC.Rings.map_mem_range_map_iff, ZInQ.Manuscript.RC.AppE32Fixed.outerWitness_of_completed_coefficients, ZInQ.Manuscript.RC.Even.E5_coefficientwise
---

# (E.5): the uniform clearing of the even scalar

Assume nothing: the Lean theorems take no named input.

Let $\Lambda=\mathbb Z_2[[t]]$, let $A=\Lambda[1/2]$ be its localization at $2$, and let $\mathscr O$ be the
completion of $\Lambda$ localized at $(2)$, realized as $\varprojlim_n(\mathbb Z/2^n)((t))$. An element of $A$
whose image in the fraction field of $\mathscr O$ lies in $\mathscr O$ lies in $\Lambda$, and conversely. Hence,
if $u\in A$ and $2^cu\in\mathscr O$, then $2^cu\in\Lambda$ with the same $c$, and coefficientwise in the group
basis of a finite group $G$,
$$A\cap\mathscr O=\Lambda,\qquad 2^{c_E}u^{\rm ev}\in\Lambda[G],\tag{E.5}$$
with no term $v_2|G|$ in the exponent.

In the manuscript the two memberships $u^{\rm ev}\in A[G]$, from (E.4a) and Fourier inversion, and
$2^{c_E}u^{\rm ev}\in\mathscr O[G]$, from the free rank-two model (E.3) and the integral wedge, come from Kato's
class; in Lean they are hypotheses. The outputs of Appendix E (`EvenFamilyOutput`, see
[the overview](README.md)) record the second membership as power series over $\mathbb Z_2$ (the field
`outer`): every coefficient of $2^{c_E}u_g$ lies in $\mathbb Z_2$, which is already the membership
$2^{c_E}u^{\rm ev}\in\Lambda[G]$. So `E5_coefficientwise` is immediate from that field and does not use
$A\cap\mathscr O=\Lambda$. The genuine theorem here is `halfToFracO_mem_range_iff`; it enters a further
Lean theorem, `outerWitness_of_completed_coefficients`, which produces the field `outer` from
characterwise bounded denominators and membership in the actual $\mathscr O$, and which the proof of
Proposition 7.2 does not use.

**Proof sketch.** Write $u=g/2^e$ with $g\in\Lambda$. If $g/2^e=y\in\mathscr O$, then $g=2^ey$ reduces to zero in
$(\mathbb Z/2^e)((t))$, so $2^e$ divides every coefficient of $g$ and $u\in\Lambda$.

The Lean proof of [Proposition 7.2](../section-7/proposition-7-2-even-scalar.md) uses `E5_coefficientwise`
for the clearing clause of (3.2). In the Lean proof of Theorem 5.3 none of these theorems is used:
(3.2) enters as a clause of the field `PreLeaves.even_upper` of
[the remaining hypotheses](../remaining-hypotheses.md).

## Depends on

- [Appendix E: the rings](README.md)

## Sources

- [Appendix E](../../../sources/manuscript.md#appendix-e)
