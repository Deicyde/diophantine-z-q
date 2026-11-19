---
declaration: theorem
origin: cited
---

# Unused-prime comparison and the corrected coordinate (4.7)

At an unused good split prime $q$, with the actual primitive-to-relaxed maps and the retained class and
functional, let $z$ be the scalar Frobenius value, $e_q=a_q-z-z^{-1}$ and $l_q$ the two-place quotient
factor. Then
$$l_qu_{\rm rel}=e_q^2\varepsilon_qu_{\rm prim},\qquad\varepsilon_q\in\Lambda^\times.\tag{4.7}$$
For a finite binary family the universal correction $\eta$ lies in $\mathscr O[G]$, and the corrected
coordinate $\widetilde u=\eta u_{\rm rel}$ satisfies $\widetilde u_x=\varepsilon_xu_{{\rm prim},x}$ at every
character, with $\varepsilon_x\in\Lambda^\times$. Wherever the primitive coordinate is regular at $t=0$, this
preserves its central valuation and its vanishing. Only the product is specialized; $\eta_x$ itself may have a
pole.

**Proof sketch.** Let $i:C_P\to C_R$ be the primitive-to-relaxed map and $j:C_S\to C_{P^\perp}$ the paired
strict-to-primitive map; at $q$ they go from the unramified to the full condition and from zero to the
unramified condition. Naturality of the cup pairing (Nekovář, 6.4.1–6.4.3) gives
$\beta_R(v,iw)=\beta_P(jv,w)$. The norm identity $z_R=e_q\,i(z_P)$ and, since conjugation sends $z$ to $z^{-1}$,
$jz_S=e_qz_{P^\perp}$ give $\lambda_R\circ i=e_q\lambda_P$, so the class and the functional each contribute one
$e_q$. The two quotient determinants multiply to
$\det(z\operatorname{Fr}_q-q)\det(z^{-1}\operatorname{Fr}_q-q)=q^4l_q$, and the support triangle in the
original integral bases gives (4.7); the unit $\varepsilon_q$ comes from comparing finite mapping-cone bases,
whose determinants are $A_i$-units and so have $\Lambda$-unit limits. With $l_q/e_q^2=1+2v_q$, the correction
is $\eta=\prod_q(1+v_q(1+g_q))$, formed before characters.

## Depends on

- [The paired functional and the class-functional coordinate](paired-functional.md)

## Proof depends on

- [Local conditions, the derived Kummer condition and duality](local-conditions.md)
- [Finite Heegner descent with one multiplier (4.1), (4.2)](finite-heegner.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:arith-common-coordinate` (L4142–4328); the
  correction $\eta$ again at L10862–10935

## Manuscript check

Mapped by AI review together with the calibration (4.6); the review reports their Euler-factor identities as
checked. The comparison is not yet checked line by line, and the locator in Nekovář (6.4.1–6.4.3) is not yet
checked against the print.
