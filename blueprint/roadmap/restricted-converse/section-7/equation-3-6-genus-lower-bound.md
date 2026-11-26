---
article_id: af_7a34d8ef25ec1b14644bfac8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.CloudB3RC53.AppGEndpoints.genusLowerF4_proof, ZInQ.Contrib.CloudB3RC53.AppGEndpoints.GenusLowerF4
---

# (3.6): the genus lower bound

Let "prepared", "simple zero" and "companion" be predicates, $L_*$, $j_{\rm gen}$, $j_{\rm rc}$ and
$s\ge0$ functions, and $h_*$, $A$, $C_R$, $C_E$, $C_{\rm per}$ numbers. Suppose that for every prepared
simple zero $h$:

- (3.3) there is a companion $k'$ of $h$ with $\omega(k')\le A$, $L_*(hk')\ne0$ and
  $v_2L_*(hk')\le2\omega(h)+2\omega(k')+s(hk')+C_E$;
- (3.4) at every companion $k'$ of $h$,
  $2j_{\rm rc}(h,k')-2j_{\rm gen}(h)=v_2L_*(hk')-v_2L_*(h_*)+C_{\rm per}+\epsilon$ with $|\epsilon|\le2$;
- (3.5) at every companion $k'$ of $h$ with $\omega(k')\le A$,
  $2j_{\rm rc}(h,k')\ge4\omega(h)+s(h)+s(hk')-C_R$.

Then every prepared simple zero $h$ satisfies
$$2j_{\rm gen}(h)\ge2\omega(h)+s(h)-C,\qquad C=2A+C_R+C_E-v_2L_*(h_*)+C_{\rm per}+2.\tag{3.6}$$

The Lean statement is the inequality of Appendix G's (F.4), over arbitrary data; it names the constant,
which the manuscript leaves implicit, and allows a period constant $C_{\rm per}$ in (3.4). The constant
does not depend on $h$.

**Proof sketch.** Combine (3.3), (3.4) and (3.5) at the companion $k'$ given by (3.3): the term
$s(hk')$ cancels, and $|\epsilon|\le2$ gives the constant.

The reduction of Theorem 5.3 uses `genusLowerF4_proof` twice: through `exists_oddMinimum`, which
attains the odd minimum, and through `finalFamilyField_proof`, behind
[Proposition 7.17](proposition-7-17-final-family.md).

## Depends on

- [Proposition 7.14: a bounded companion (3.3)](proposition-7-14-rough-companion.md)
- [(3.4): the height comparison](equation-3-4-height-comparison.md)
- [(3.5): the arithmetic lower bound](equation-3-5-arithmetic-lower-bound.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
