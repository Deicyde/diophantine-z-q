---
declaration: theorem
origin: cited
---

# One moving character for the complete active list

Fix an allowed $K$ and any finite list of oriented active primes. For every $n,B\ge1$ and every finite
avoidance set there are infinitely many split rational primes $r\equiv1\pmod{2^B}$ and characters
$\xi:\operatorname{Gal}(H_r/K)\to\mathbb Z/2^n\mathbb Z$ of the ring class group of conductor $r$ that are
surjective on inertia at $r$, trivial on the decomposition groups at $2N$, and take the value one at every
prescribed active orientation, with
$$v_2(2\pm a_r)\le c_E,\qquad v_2\det(1\pm\operatorname{Fr}_r)\le c_E,$$
where $c_E$ depends only on the fixed Tate image, not on $K$, $n$, $B$ or the active list. One such character
serves the whole binary family before evaluation.

**Proof sketch.** Choose prime ideals in distinct conjugate pairs (the active orientations, one above each
prime of $2N$, and enough split primes to generate $\operatorname{Cl}(K)$), weights $w_j=1$ at the active
primes and $0$ elsewhere, a basis $m^{(a)}$ of the relations in $\operatorname{Cl}(K)$, and generators
$\alpha_a=\beta_a/\overline\beta_a$. Over $K(\mu_{2^\infty})$ prescribe the action
$\zeta_{2^n}^{-\sum_jm^{(a)}_jw_j}$ on $\alpha_a^{1/2^n}$ (4.4a); it respects every Kummer relation because
the relevant cyclotomic layers are unramified at the odd weighted primes. A prime $r$ with this radical
Frobenius gives the compatibility $\kappa_r(\operatorname{res}\alpha_a)=-\sum_jm^{(a)}_jw_j$ (4.4b), so the
values $\xi(\mathfrak q_j)=w_j$ and the power-residue character at $r$ extend to $\xi$. For the trace bound,
Serre's open image theorem gives $\Gamma_d\subset\rho_T(G_{\mathbb Q(\mu_{2^\infty})})$ for a fixed $d\ge2$;
unipotent identities give $\Gamma_{2d+2}$ in the image over $K(\mu_{2^\infty})$ and $\Gamma_\nu$, $\nu=8d+10$,
in the image of the radical-fixing kernel (4.4c). In $\operatorname{SL}_2(\mathbb Z_2)$, one of
$A$, $AU(2^\nu)$, $AD(1+2^\nu)$, $AD(1+2^{\nu+1})$ has trace at distance of valuation at most $2\nu+1$ from
both $2$ and $-2$ (4.4d). Chebotarev then gives $r$ with $c_E=2\nu+1=16d+21$, and $n_i\ge2i$ makes
$\Psi_i=(1+t)^{\xi_i}$ a character with values in $A_i$.

## Depends on

None.

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:arith-moving-character` (L3500–3702)

## Manuscript check

Mapped by AI review. The $\operatorname{SL}_2(\mathbb Z_2)$ group theory and the trace lemma (4.4d) were
checked numerically. The construction of the moving primes and characters is not yet checked line by line;
the later checks used only the bound $c_E$. The locator of Serre's open image theorem is not yet checked
against the print.
