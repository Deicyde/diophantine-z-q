---
article_id: af_9d89b9c570bda987f7a1c44b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.GlueSweep.Even.E4a_of_smith, ZInQ.Manuscript.RC.Even.E4a_nonneg, ZInQ.Manuscript.RC.GlueSweep.Even.length_coker_eq_addVal_det
---

# (E.4a): the height-one valuations of the even scalar

Assume three steps of the manuscript, taken as hypotheses of the Lean theorem and not proved: the
inverse-determinant identity $v_{\mathfrak p}(u^{\rm ev}_x)=v_{\mathfrak p}(\alpha)-v_{\mathfrak p}(\det X)$;
the index identity $\ell_R(H^1/Rz)=v_{\mathfrak p}(\alpha)$ for $z=\alpha e$ in the free module $H^1=Re$;
and the inequality (K2), $\ell_RH^2\le\ell_R(H^1/Rz)$, which the manuscript derives from Kato's bound.

Let $R=A_{\mathfrak p}$ be the localization of $A=\Lambda[1/2]$ at a height-one prime, a discrete
valuation ring, and let $H^2$ be the cokernel of a square differential $X$ over $R$ with
$\det X\ne0$. Then
$$v_{\mathfrak p}(u^{\rm ev}_x)=\ell_R\bigl(H^1/Rz\bigr)-\ell_RH^2\ \ge\ 0.\tag{E.4a}$$

The manuscript writes $\sum_iv_{\mathfrak p}(d_i)$ over the Smith entries of a finite free model of the
positive complex; Lean takes the degree-two differential as one square matrix. The Lean statement is
about integers standing for these valuations and lengths: it does not construct $u^{\rm ev}_x$, the
positive complex or Kato's class, and only the Smith step is proved for an actual matrix.

**Proof sketch.** Over a discrete valuation ring the Smith normal form gives
$\ell_R(R^n/XR^n)=v(\det X)$, which is the sum of the valuations of the Smith entries. Substituting
this and the index identity, the inequality is (K2).

In the Lean proof of Theorem 5.3 this theorem is not used. The membership $u^{\rm ev}_x\in\Lambda[1/2]$
that (E.4a) yields is the field `charEval_mem` of `EvenFamilyOutput`, the per-family part of
`AppEOutputs` (see [the overview](README.md)), and no Lean theorem derives that field from this one.

## Depends on

None.

## Sources

- [Appendix E](../../../sources/manuscript.md#appendix-e)
