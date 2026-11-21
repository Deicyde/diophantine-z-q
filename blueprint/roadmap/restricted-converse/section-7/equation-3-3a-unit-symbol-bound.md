---
article_id: af_28f41b9fa3fb115f2fd5c463
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.CloudB3RC53.EvenUpper.h33a_of_F1, ZInQ.Contrib.CloudB3RC53.EvenUpper.UnitMin
---

# (3.3a): the bound at a unit of the even symbol

Assume two outputs of Appendix E for the coefficients $a(D)$ of the even source (named inputs, not
proved): $L_*(D)\ne0$ exactly when $a(D)\ne0$, and then $v_2L_*(D)=2v_2a(D)+\kappa$; and
$v_2a(D)-\omega(D)\ge c$ at every $D$ with $a(D)\ne0$, some such $D$ existing and none of them zero.
Call $p$ a *unit of the normalized even symbol* if $a(p)\ne0$ and $v_2a(p)-\omega(p)$ is the minimum of
$v_2a(D)-\omega(D)$ over the nonzero coefficients. Then there is $C_0$ such that every unit $p$ satisfies
$$L_*(p)\ne0,\qquad v_2L_*(p)\le2\omega(p)+C_0.\tag{3.3a}$$

Here $L_*$ is the interface datum of [the remaining hypotheses](../remaining-hypotheses.md); the
normalized symbol is read through the attained minimum, as in Appendix G.

**Proof sketch.** The lower bound makes the minimum $\delta_e$ of $v_2a(D)-\omega(D)$ attained. At a
unit, $v_2a(p)=\delta_e+\omega(p)$, so the coefficient-square formula gives
$v_2L_*(p)=2\omega(p)+2\delta_e+\kappa$, and $C_0=2\delta_e+\kappa$.

In the Lean proof of Theorem 5.3, (3.3a) is not obtained from this theorem: it is a clause of the field
`PreLeaves.even_upper` of the remaining hypotheses.

## Depends on

- [Section 7: coefficient symbols](README.md)
- [The remaining hypotheses](../remaining-hypotheses.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
