---
article_id: af_b24820f406b17f8219d58197
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.CloudB3RC53.AuxFactor.F1_unit
---

# (F.1): the central value at a unit of the normalized even symbol

Fix one even source with coefficients $a(D)$ and sign $\sigma$. Assume two outputs of Appendix E for it,
taken as inputs here (ELLIOT): (E.11), that $L_*(\sigma D)\ne0$ exactly when $a(D)\ne0$, and then
$v_2L_*(\sigma D)=2v_2a(D)+\kappa_e$; and a lower bound $v_2a(D)-\omega(D)\ge c$ at every $D$ with
$a(D)\ne0$, which the manuscript draws from (E.9). Assume also that some coefficient is nonzero. Then the
integers $v_2a(D)-\omega(D)$, over the nonzero coefficients, have an attained minimum $\delta_e$, and
every $D$ attaining it, that is every unit of the normalized symbol, satisfies
$$L_*(\sigma D)\ne0,\qquad v_2L_*(\sigma D)=2\omega(D)+C_{e,\rm unit},\qquad
C_{e,\rm unit}=2\delta_e+\kappa_e.\tag{F.1}$$

The Lean statement is over an arbitrary index set, with the coefficients, the central values and their
valuations as functions; the source and the sign are not formalized there. The constant belongs to the
fixed source.

In the reduction of Theorem 5.3, (F.1) is not taken from this theorem. At the prepared even sources its
consequence [(3.3a)](../section-7/equation-3-3a-unit-symbol-bound.md) is a clause of the field
`PreLeaves.even_upper`; at the transported source of the final companion the field `PostLeaves.address`
has an even reading clause, which its docstring describes as the conclusion of (F.1) for the chosen
reading. Both fields are in [the remaining hypotheses](../remaining-hypotheses.md).

**Proof sketch.** The lower bound and the nonzero coefficient make the set of values
$v_2a(D)-\omega(D)$ nonempty and bounded below, so it has a least element $\delta_e$. At a unit,
$v_2a(D)=\omega(D)+\delta_e$, and (E.11) gives the nonvanishing and the valuation.

## Depends on

- [Appendix G: the normalized even symbol](README.md)

## Sources

- [Appendix G](../../../sources/manuscript.md#appendix-g)
