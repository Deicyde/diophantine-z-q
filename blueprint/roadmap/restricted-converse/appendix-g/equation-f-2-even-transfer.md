---
article_id: af_4b04c2da6839c89acb231ca0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.CloudB3RC53.AuxFactor.F2_bound
---

# (F.2): the even upper bound at a parameter of corank zero

Fix one even source with coefficients $a(D)$, and call $x$ a unit if $a(x)\ne0$ and
$v_2a(x)-\omega(x)=\delta$. Assume, with no input proved here:

- (E.11) of Appendix E (ELLIOT), as on the page of [(F.1)](equation-f-1-even-unit.md);
- the forward rank-zero implication (PRINT): $L_*(p)\ne0$ gives Selmer corank zero;
- (E.8) of Appendix E (ELLIOT) for the even scalar $u(p)=u^{\rm ev}_p(0)$ at every $p$ of corank zero:
  $u(p)=0$ exactly when $L_*(p)=0$, and otherwise $|v_2u(p)-(v_2L_*(p)-2\omega(p)-s(p))|\le C_{\rm loc}$;
- the Boolean comparison at $d$ (ELLIOT): for every $M$ there is a unit $x$ with $u(x)=u(d)$ or
  $v_2(u(x)-u(d))\ge M-c_E$.

Then a parameter $d$ of corank zero has $L_*(d)\ne0$ and
$$v_2L_*(d)-2\omega(d)-s(d)\le C_{e,\rm unit}+2C_{\rm loc},\qquad C_{e,\rm unit}=2\delta+\kappa_e.\tag{F.2}$$

In the manuscript $d$ is partitionable, and the units come from the cubes $d_x$ of the one-symbol address
construction ([Lemma 7.11](../section-7/lemma-7-11-one-symbol-address.md)) with the Boolean comparison
of Section 9. The Lean statement takes the comparison at $d$ as a hypothesis, so partitionability does
not appear. With $\delta=\delta_e$, this is [(3.3b)](../section-7/proposition-7-13-even-upper-bound.md)
with an explicit constant.

The reduction of Theorem 5.3 does not use this theorem: (3.3b) is derived there from the field
`PreLeaves.even_upper` of [the remaining hypotheses](../remaining-hypotheses.md), as on the page of
Proposition 7.13.

**Proof sketch.** Put $B_e=C_{e,\rm unit}+C_{\rm loc}$ and take $M>B_e+c_E$. A unit $x$ has
$L_*(x)\ne0$ and $v_2L_*(x)=2\omega(x)+C_{e,\rm unit}$ by (E.11), so it has corank zero, and (E.8) gives
$u(x)\ne0$ and $v_2u(x)\le B_e$. If $u(d)$ were zero or had valuation above $B_e$, the unit given by
the comparison would contradict this bound. So $u(d)\ne0$, which gives $L_*(d)\ne0$, and (E.8) at $d$
gives (F.2).

## Depends on

- [Appendix G: the normalized even symbol](README.md)
- [(F.1): the central value at a unit of the normalized even symbol](equation-f-1-even-unit.md)

## Sources

- [Appendix G](../../../sources/manuscript.md#appendix-g)
