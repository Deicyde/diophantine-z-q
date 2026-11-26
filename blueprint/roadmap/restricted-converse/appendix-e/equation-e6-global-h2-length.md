---
article_id: af_6d7acb79120fde3c55d5ae14
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Even.E6_length
---

# (E.6): the length of global $H^2$

Assume an exact sequence of the shape below with the given lengths (a hypothesis of the Lean theorem;
in the application it is part of the input `CentralLengthInput` of
[(E.7)](equation-e7-central-valuation.md), whose docstring makes it ELLIOT, with the local lengths
from local Tate duality and Pontryagin duality as GLUE). The theorem takes no named input.

Let $E^h$ be a corank-zero constituent, $T=T_2(E^h)$ and $D=E^h[2^\infty]$. Suppose the sequence of
orthogonal Kummer duality with its real terms,
$$0\to L_2/J_2\to\mathrm{Sel}_{2^\infty}(E^h/\mathbb Q)^\vee\to H^2_{\rm glob}\to
\bigoplus_{v}H^2(\mathbb Q_v,T)\oplus H^2(\mathbb R,T)\to H^0(\mathbb Q,D)^\vee\to0,$$
is exact, with lengths $i$, $s(h)$, $\sum_vg_v$, $r_2$ and $g$ at the known terms. Then $H^2_{\rm glob}$ has
finite length and
$$\ell H^2_{\rm glob}=s(h)-i+\sum_vg_v+r_2-g.\tag{E.6}$$

The Lean statement is the length count for any exact sequence of this shape over any ring. That the
sequence above is exact with these lengths (Poitou–Tate in Nekovář's form, local Tate duality, and
$\mathrm{Sel}_{2^\infty}=Ш[2^\infty]$ at corank zero) is not proved.

**Proof sketch.** Length is additive along exact sequences; the alternating sum over the five terms
vanishes, and the known lengths are finite.

In the Lean proof of Theorem 5.3 this theorem is not used.

## Depends on

None.

## Sources

- [Appendix E](../../../sources/manuscript.md#appendix-e)
