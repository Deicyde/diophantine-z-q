---
article_id: af_262e06d04efc7c9e5f92d173
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Even.padicValNat_sF_smoothing, ZInQ.Manuscript.RC.Even.smoothing, ZInQ.Manuscript.RC.Even.sF, ZInQ.Manuscript.RC.Even.smoothing_modEq_one
---

# (K5)–(K6): the retained smoothing and its central scalar

Assume nothing: the statement is arithmetic, and the Lean theorems take no named input.

Let $e\ge1$ and let $N_{\rm odd}$ and $F$ be odd. The one smoothing choice for the whole family is
$$c=d_s=1+2^e\cdot3N_{\rm odd}F,\tag{K5}$$
so $c\equiv1\pmod{3N_{\rm odd}F}$, and the central scalar of the retained-smoothed classes is
$$s_F=(c^2-c)(d_s^2-d_s)=c(c-1)\,d_s(d_s-1),\qquad v_2(s_F)=2e.\tag{K6}$$
The valuation does not depend on $F$.

The manuscript takes $e\ge\max\{3,v_2(N)\}$; the valuation needs only $e\ge1$. In Lean (K5) is a
definition (`smoothing`) and the congruences of the surrounding paragraph are separate lemmas
(modulo $2^{e+1}$, modulo $2^vN_{\rm odd}$ for $v\le e$, modulo $8$ for $e\ge3$). That Kato's
retained-smoothed central value carries exactly the scalar $s_F$ is not formalized.

**Proof sketch.** Here $c$ is odd and greater than one, so $v_2(c^2-c)=v_2(c-1)=e+v_2(3N_{\rm odd}F)=e$,
and the same holds for $d_s$.

In the Lean proof of Theorem 5.3 this theorem is not used: the smoothing lives inside the step
`AppEFromKato` described in [the overview](README.md).

## Depends on

None.

## Sources

- [Appendix E](../../../sources/manuscript.md#appendix-e)
