---
declaration: theorem
origin: cited
---

# Visibility and the native genus index (O.8)

For the odd forms and unaveraged points above there is one constant $C_{\rm det}$, independent of the stage and
of the admissible $D$, such that
$$\begin{aligned}v_2a_M(D)&\ge\min\{M,\,j_{\rm gen}(D)-C_{\rm det}\}&&\text{for a known simple-zero }D,\\
v_2a_M(D)<M&\ \Longrightarrow\ \operatorname{ord}_{s=1}L(E^{(D)},s)=1,\quad j_{\rm gen}(D)\le v_2a_M(D)+C_{\rm det}&&\text{for every admissible }D.\end{aligned}\tag{O.8}$$
If an admissible $D$ of odd sign is not a simple zero, its coefficient vanishes modulo $2^M$. No genus index of a
torsion point is defined or used.

**Proof sketch.** For a known simple zero write $P_D=m_DG+T$ in its native rank-one lattice; $L$ kills $T$, and an
integral finite-field Kummer map cannot decrease $v_2(m_D)$, so (O.7) gives the lower bound by the native index.
The rational free line has index at most two in the native lattice, by conjugation and the norm; this and the
fixed period convention go into $C_{\rm det}$. If an odd-sign $D$ is not a simple zero, the height formula
(Theorem 1.1 of Cai–Shu–Tian, for the Rankin product $L(E^{(D)},s)L(E^{(h_*)},s)$ with $L(E^{(h_*)},1)\ne0$) makes the
genus point torsion, so $L$ kills it and the coefficient is zero modulo $2^M$. Hence a coefficient of valuation
below $M$ forces a simple zero, and then the first inequality applies.

## Depends on

- [The unaveraged weighted theta comparison (O.7)](theta-comparison.md)

## Proof depends on

- [One witness and a compatible detecting sequence (3.7), (O.2)](odd-witness.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:app-visibility` (L9407–9445)

## Manuscript check

Read in full by AI review. The height formula is used only qualitatively, height zero exactly when the
derivative vanishes, which does not depend on the conductor factor discussed under (3.4). The case $D=1$, used for
the first branch of the proof of Theorem 5.3, is covered explicitly (L8261–8266, L9189–9190). For
$(D/\ell_0)\ne1$ the coefficient is zero and (O.8) holds trivially. The statement of Cai–Shu–Tian's Theorem 1.1 is
not yet checked against the print.
