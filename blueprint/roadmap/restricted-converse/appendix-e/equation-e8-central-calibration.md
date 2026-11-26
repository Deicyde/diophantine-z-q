---
article_id: af_8743eb8a6b5855c688075520
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Even.ConstituentOutput.E8, ZInQ.Manuscript.RC.Even.ConstituentOutput, ZInQ.Manuscript.RC.Even.E8_omega, ZInQ.Manuscript.RC.Even.E8_of_E7_K3
---

# (E.8): the central calibration of the even scalar

Assume the data of one corank-zero constituent with nonzero central value (`ConstituentOutput`, the
manuscript's own steps with standard readings, not proved): the exact sequences of
[(E.7)](equation-e7-central-valuation.md); the formula (K3) for the retained class
$z=F_E(Z_F)_h$, with the smoothing and old-support factors absorbed,
$$v_2\exp^*z=v_2L_*(h)+\sum_{q\ \rm unused}v_2\#E^h(\mathbb F_q)+\epsilon_{\rm rec},\qquad|\epsilon_{\rm rec}|\le C_E;$$
$g_q=v_2\#E^h(\mathbb F_q)$ at the unused good primes and $g_q=2$ at the active good primes; and fixed
bounds for $g_v$ at the places dividing $2N$, for $g$, $r_1$ and $e_2$. Then, with $C_{\rm loc}$ depending
only on these fixed bounds and on $\omega(N)$,
$$v_2u^{\rm ev}_h(0)=v_2L_*(h)-2\omega(h)-s(h)+\epsilon_h,\qquad|\epsilon_h|\le C_{\rm loc}.\tag{E.8}$$

Lean first proves the bound with the number of active good primes of $h$ in place of $\omega(h)$, with
the constant $C_E+|{\rm fix}|\,C_{\rm fix}+2C_g+1+C_r+C_e$, and then passes to $\omega(h)$ at the cost
$2\omega(N)$. In the structure the numbers $v_2\#E^h(\mathbb F_q)$ are an arbitrary recorded function,
so (K3) is an identity between recorded integers, not a statement about Kato's class. The facts behind
$g_q=2$ are proved (inertia acting by $-1$ fixes exactly the $2$-torsion, and $E_\ell^{(h)}$ has four
$2$-torsion points), but the identity itself is a field.

**Proof sketch.** Split $\sum_vg_v$ in (E.7) over the active, unused and fixed places. The unused terms
cancel against (K3), each active prime contributes $2$, and what remains is bounded by the fixed
constants. The number of active good primes differs from $\omega(h)$ by at most $\omega(N)$.

The Lean proof of [Proposition 7.2](../section-7/proposition-7-2-even-scalar.md) uses this theorem for
the central clause of (3.2). In the Lean proof of Theorem 5.3 it is not used: (3.2) enters as a clause
of the field `PreLeaves.even_upper` of [the remaining hypotheses](../remaining-hypotheses.md).

## Depends on

- [Appendix E: the positive complex and the even scalar](README.md)

## Proof depends on

- [(E.7): the central valuation before the local terms](equation-e7-central-valuation.md)

## Sources

- [Appendix E](../../../sources/manuscript.md#appendix-e)
