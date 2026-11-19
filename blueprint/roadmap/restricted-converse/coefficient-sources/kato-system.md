---
declaration: theorem
origin: cited
---

# One retained Kato system and its two comparisons (K1)–(K3)

Let $E/\mathbb Q$ be the fixed non-CM curve, $T=T_2E$, $\Lambda=\mathbb Z_2[[\Gamma]]=\mathbb Z_2[[t]]$ for the real
cyclotomic Galois group $\Gamma$, $\kappa:G_{\mathbb Q}\to\Gamma$ the quotient map and $A=\Lambda[1/2]$. Fix
$e\ge\max\{3,v_2(N)\}$. Let $G$ be a finite elementary abelian two-group, $\psi:G_{\mathbb Q}\to G$ continuous,
and $\chi_x=\chi_0(x\circ\psi)$ a family of quadratic characters with one real sign and fixed local
squareclasses at $2N$, whose varying conductor primes are good and odd; let $F$ be the squarefree least common
multiple of the odd parts of their conductors. There is a single retained-smoothed class
$$Z_F\in2^{-c_E}H^1\bigl(G_{\mathbb Q,S},T\otimes\Lambda[G]\,(\chi_0\psi\kappa^{-1})\bigr),\qquad S=\operatorname{prime}(2NF),\tag{K1}$$
with $c_E$ fixed before $F$ and $G$, and one $F_E\in\Lambda$ with $F_E(0)\ne0$, fixed before $F$ and $G$, such that
at every height-one prime $\mathfrak p$ of $A$
$$\ell_{A_{\mathfrak p}}H^2(C_{S,x})_{\mathfrak p}\le\ell_{A_{\mathfrak p}}\bigl(H^1(C_{S,x})/AF_E(Z_F)_x\bigr)_{\mathfrak p},\tag{K2}$$
where $C_{S,x}$ is the rational global Iwasawa complex of the constituent; and, for an odd squarefree signed
parameter $h$ with $\chi_x=\chi_h$ and nonzero central value,
$$v_2\exp^*\bigl(F_E(Z_F)_x(0)\bigr)=v_2L_*(h)+\sum_{q\mid F,\ q\nmid h}v_2\#E^h(\mathbb F_q)+2e+v_2F_E(0)+\epsilon_h,\tag{K3}$$
with $\epsilon_h$ in a bounded set depending only on the fixed data. A zero central value gives zero dual
exponential.

**Proof sketch.** Choose one symbol combination with nonzero projections to both real signs, and smoothing
constants $c=d_s\equiv1\pmod{3N_{\rm odd}F}$, $\equiv1+2^e\pmod{2^{e+1}}$ (K5), so that Kato's explicit
reciprocity contributes valuation $2e$ independent of $F$ (K6). Kato's integral maps, with $j_*$ cohomology
taken modulo each power of two, give classes whose inertia restrictions vanish integrally (Leray), and the
Mackey formula keeps this through ramified corestriction (K7). Primitive twisting gives an Euler system with
the unused-prime factors $E_q=P_q(q^{-1}\sigma_q^{-1})$ (K8)–(K9), and the coefficient map assembles one class
$Z_F$ (K10), (E.1)–(E.2). The central trace with Kato's Theorems 6.6 and 9.7, descended through the basis
$\sqrt h\,e_\chi$, gives the normalization (K12)–(K14), with no factor $\varphi(D)$ or $2^{\omega}$. The
hypotheses of Kato's Theorem 13.4(2) hold (nonzero generic sign components by 13.5(2), rank-one eigenspaces,
irreducibility, and the open-image condition), which gives (K15), and a cone from the $j_*$ condition to full
cochains with a length count proves (K2) (K16).

## Depends on

None.

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:app-kato-system` (L6832–7361)

## Manuscript check

Mapped by AI review and read once for structure; not yet checked line by line. The smoothing valuation
$v_2s_F=2e$ was checked by script. The normalization (K14), with no factor $\varphi(D)$ or $2^{\omega}$, is the
even-side counterpart of the conductor factor discussed under (3.4); the manuscript argues it explicitly
(L7148–7160, L7350–7361). Not yet checked against the print: the many Kato locators, in particular Theorem
13.4(2) under rational hypotheses at $p=2$ (part (3) is not used), and the open-image condition, for which the
manuscript relies on Serre without citing it at that point.
