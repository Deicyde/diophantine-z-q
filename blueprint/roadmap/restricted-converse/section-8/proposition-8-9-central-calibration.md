---
article_id: af_7b77afd560677592a7fc6301
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Wiring.calibrationTarget_of_H, ZInQ.Manuscript.RC.Wiring.CalibrationTarget, ZInQ.Manuscript.RC.Central.calibration_46
---

# Proposition 8.9: arithmetic calibration at known simple zeros (4.6)

Assume $\ell>0$, [the cited results](../printed-results.md) (Kolyvagin's theorem, for the free generators
of the rank-one Mordell–Weil lattices) and the field `PostLeaves.calibration` of [the remaining
hypotheses](../remaining-hypotheses.md) (ELLIOT, PRINT and GLUE): at every address with the two analytic
hypotheses below, the two-primary Ш and torsion orders (with Kolyvagin), good models at the primes of
$k$ with Edixhoven's component count, the pullback and period comparison, Cassels' isogeny invariance in
Milne's form at the canonical regulators, the moving prime in the output form of Proposition 8.5, and a
triangular Kummer model whose quotient block is the sum of the local blocks at the moving and active
places.

Then there is $C_{\rm cal}$ such that for every family of [(3.9)](../section-7/proposition-7-17-final-family.md)
and every address $x$ with $\operatorname{ord}_{s=1}L(E^{(h_x)},s)=1$ and $L(E^{(h_xk)},1)\ne0$ there are
integers $0\le t_p\le2$ and $|\epsilon|\le C_{\rm cal}$ with
$$v_2u_{{\rm prim},x}(0)=2j_{\rm rc}(h_x,k)-4\omega(h_x)-s(h_x)-s(h_xk)-\sum_{p\mid k}t_p+\epsilon.\tag{4.6}$$

The manuscript states (4.6) for every $h$ with the ring-class hypotheses whose primes split in
$K=\mathbb Q(\sqrt k)$; the Lean statement is asked only at the addresses of the final families, where
$u_{\rm prim}$, $j_{\rm rc}$ and $k$ are interface data of the remaining hypotheses. The $t_p$ are
existential with $t_p\le2$; the manuscript also notes $t_p=2$. The error bound is
$C_{\rm cal}=2v_2L+2G_0+5$, with $L$ the fixed multiplier and $G_0$ a torsion bound. The docstring of
the field records that it is conclusion-shaped in part: its local-block Kummer model is equivalent to
the valuation formula before Milne's identity is applied, and the Milne, period, moving-prime and
Kummer-model data are existential, not tied to the genuine objects. The field is also asked in the
branch where the odd symbol is a unit at the empty configuration, where the manuscript does not build
these objects.

The reduction of Theorem 5.3 takes (4.6) twice in `rcSteps_of_leaves`: from this theorem for the step
`RCSteps.calibration` (`calibrationTarget_of_H`, applied to `PostLeaves.calibration`), and at the
companion pairs, for (3.5), directly from the field `PreLeaves.eq35` (`eq35Target_of_inputsAR`).

**Proof sketch.** The class and the functional each contribute $j_{\rm rc}+v_2L+v_2m$ (Lemma 8.8's
valuation, built into the field's Kummer model), the Kummer torsion contributes $2g_{\mathcal A}-s_{\mathcal A}$
and the local quotients $-2v_2N-4\omega(h)$, with $v_2N=v_2m$, so the moving-prime terms cancel. Milne's
identity for the sum and difference isogenies converts $s_{\mathcal A}$ into $s(h)+s(hk)$ plus the
regulator ratio ($v_2=\pm1$), the period ratio (at most $4$ in absolute value), twice the torsion of
$E^{(h)}\times E^{(hk)}$ (bounded) and the component ratio, which Edixhoven's count makes $\sum_{p\mid k}t_p$.

## Depends on

- [The cited results](../printed-results.md)
- [The remaining hypotheses](../remaining-hypotheses.md)
- [Section 8: actual classes, local conditions and central comparison](README.md)
- [Proposition 7.17: one family for the two coefficient tests (3.9)](../section-7/proposition-7-17-final-family.md)

## Sources

- [Section 8](../../../sources/manuscript.md#section-8)
