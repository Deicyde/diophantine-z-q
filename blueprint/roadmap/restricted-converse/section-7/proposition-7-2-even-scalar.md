---
article_id: af_8adc9088e26a303a67bf21de
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.GlueSweep.Even.evenScalar32_of_kato_ecurve, ZInQ.Manuscript.RC.Even.evenScalar32_of_appE, ZInQ.Manuscript.RC.Even.EvenScalar32, ZInQ.Manuscript.RC.Even.unusedFactor_central
---

# Proposition 7.2: the fixed-form even scalar (3.2)

Assume Kato's construction of zeta elements for elliptic curves without complex multiplication
(`KatoZetaLeaf`, a printed result that is not one of [the cited results](../printed-results.md)), that a
rational CM $j$-invariant is an integer (`CMjInteger`, a reading of the literature), and the
construction of Appendix E on Kato's classes (`AppEFromKato`, the manuscript's own step, not proved).

Let $\ell>0$, $E=E_\ell$, $N\ne0$, and fix a normalization of the central values: periods
$\Omega^\pm>0$ and rational numbers $L_*(h)=\sqrt{|h|}\,L(E^{(h)},1)/\Omega^{\operatorname{sign}h}$.
Then there are constants $C_{\rm ev}$ and $C$ such that for every admissible binary family
$(h_x)_{x\in\mathbb F_2^b}$ (odd squarefree parameters with one sign, $h_xh_0$ a square in $\mathbb Q_p$
for every $p\mid2N$, and $h_{x+y}h_xh_yh_0$ a square) there is
$u^{\rm ev}=\sum_{g}u_g\,g$ with $u_g\in\mathbb Q_2[[t]]$ such that, writing $u_x=\sum_g x(g)u_g$ and
$s(h)$ for the length of $Ш(E^{(h)}/\mathbb Q)[2^\infty]$:

- $2^{C_{\rm ev}}u_g\in\Lambda=\mathbb Z_2[[t]]$ for every $g$;
- if $\operatorname{corank}_{\mathbb Z_2}\mathrm{Sel}_{2^\infty}(E^{(h_x)}/\mathbb Q)=0$, then
  $u_x(0)=0\iff L_*(h_x)=0$;
- if moreover $L_*(h_x)\ne0$, then
  $$\bigl|\,v_2u_x(0)-\bigl(v_2L_*(h_x)-2\omega(h_x)-s(h_x)\bigr)\bigr|\le C.\tag{3.2}$$

The manuscript takes $N$ to be the conductor of $E$; the Lean statement allows any level $N\ne0$ and
fixes the constants after $N$ and the normalization, before the family.

The unused-prime factor (3.1), $E_q(\chi)=1-a_q\chi(q)q^{-1}\sigma_q^{-1}+q^{-1}\sigma_q^{-2}$, is not a
separate statement in Lean: at the centre it equals $(q+1-\chi(q)a_q)/q$, whose $2$-adic valuation for
odd $q$ is that of $q+1-\chi(q)a_q$ (`unusedFactor_central`).

**Proof sketch.** Lean formalizes only the last step of the manuscript's proof: from the outputs of
Appendix E (`AppEOutputs`, which `AppEFromKato` supplies from Kato's elements), characterwise
divisibility and Fourier inversion put $u^{\rm ev}$ in $\Lambda[1/2][G]$ without estimating the Fourier
denominator, and intersecting coefficientwise with the integral result gives
$2^{C_{\rm ev}}u^{\rm ev}\in\Lambda[G]$. The central identity is the local formula of Appendix E at each
corank-zero constituent, with the count of active primes replaced by $\omega(h)$ at the cost of
$2\omega(N)$. The construction itself (Kato's integral classes, the positive complex and the wedge
with a connecting class) is inside `AppEFromKato`.

In the Lean proof of Theorem 5.3, (3.2) is not obtained from this theorem: it enters as a clause of the
field `PreLeaves.even_upper` of [the remaining hypotheses](../remaining-hypotheses.md).

## Depends on

None.

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
