---
article_id: af_2c7df2b4f1966e16317d5e48
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.KummerMaps.conjActualSelmerDuality_of_prints, ZInQ.Manuscript.RC.KummerMaps.conjActualSelmerDuality
---

# Lemma 8.2: conjugate coefficients and finite Selmer duality

Assume printed results that are not inputs of the reduction of Theorem 5.3: Milne's local Tate duality
for elliptic curves over $p$-adic fields (`MilneLocalTateDualityKummerCharZero`) and Nekovář's
Propositions 5.2.4, 5.4.3 and 7.5.6 with his finite local traces (`NekovarProp524`, `NekovarProp543T`,
`NekovarProp756`, `NekovarFiniteTraces`), all PRINT. Assume also the full $2^i$-torsion of the curve over
the maximal extension unramified outside $S_0$ (GLUE), the $2^i$-th roots of unity there (`hμ₀`, which
follows from the full torsion: `conjC_hμ₀_of_fullTorsion`), that complex conjugation preserves $S_0$, the
set $P$ of Kummer places, the twist and the curve (definitions and GLUE: they are rational), that
$\alpha_i^\tau=\alpha_i^{-1}$ (ELLIOT), and that $\alpha_i$ is locally quadratic at $P$ (ELLIOT: $\Psi_i$
is trivial at $2N$).

Let $K$ be a totally complex number field, $S_0\subseteq S$ finite sets of finite places with the places
above $2$ in $S_0$, $\tau$ a complex conjugation, $A_i=(\mathbb Z/2^i)[t]/(t^i)$ and
$M_i=(T_2E\otimes A_i)(\alpha_i)$, with the $A_i$-pairing $(v,w)\mapsto e_2(v,\rho_T(\tau)w)$,
$M_i\times\tau^*M_i\to A_i(1)$, which the proof shows is perfect (`conjPairing_bijective`). Let $U$ be
the Kummer condition on $P\subseteq S_0$ (the places over $2N$ in the manuscript), the full condition at
the rest of $S_0$ and the unramified condition off $S_0$, and $U^\perp$ on $\tau^*M_i$ the conditions
transported from the conjugate places. Then there are local traces and a normalized global trace for
which $U$ and $U^\perp$ are exact orthogonal complements and
$$C_U(M_i)\simeq R\operatorname{Hom}_{A_i}(C_{U^\perp}(\tau^*M_i),A_i)[-3].$$

The manuscript works over $A_i$ or $A_i[G]$, with derivative-prime conditions as well; the Lean
statement is over $A_i$, with Kummer, full and unramified conditions only, and it uses $\tau^*M_i$
with the twisted Weil pairing in place of $M_i^*(1)$.

The reduction of Theorem 5.3 does not use this theorem.

**Proof sketch.** The pairing is perfect because $\rho_T(\tau)^2=1$, the two characters multiply to one
and $e_2$ transforms by the cyclotomic character. Place by place the transported conditions are the
orthogonal complements: at the Kummer places by Milne's duality, full against zero at the other places of
$S_0$, and unramified against unramified off $S_0$ by Nekovář 7.5.6. Nekovář's global duality 5.4.3 with
the traces then makes the Selmer duality map a quasi-isomorphism.

## Depends on

- [Section 8: actual classes, local conditions and central comparison](README.md)

## Sources

- [Section 8](../../../sources/manuscript.md#section-8)
