---
declaration: theorem
origin: cited
---

# Local conditions, the derived Kummer condition and duality

Keep the fixed $E$, $\pi$, Tate lattice and old local types, a binary group $G$ with one real sign and common
local squareclasses at $2N$, and the moving character $\Psi_i$, trivial at $2N$. Let $R_i=A_i$ or $A_i[G]$ and
let $\tau$ be a complex conjugation.

1. *(Derived Kummer condition.)* For the local twist $B=E^{(h)}$ over $F=K_v$, the condition
   $U_F=B(F)^\wedge_2[-1]\to R\Gamma(F,T_2B)$ keeps the finite two-primary torsion: modulo $2^a$ it has
   $B(F)[2^a]$ in degree zero and $B(F)/2^aB(F)$ in degree one. Its Kummer image is its exact local
   annihilator, with integral isotropy homotopies, and at $v\mid2N$ the scalar and binary versions are
   derived coefficient extensions of the same fixed local data.
2. *(Conjugate duality.)* The pairing $(v,w)\mapsto e_2(v,\rho_T(\tau)w)$ identifies $\tau^*M_i$ with
   $M_i^*(1)$, $R_i$-linearly, fixing $t$ and the group-ring basis. With conjugate places, orthogonal local
   conditions and their isotropy homotopies, the Selmer complex
   $$C_U=\operatorname{Cone}\Bigl(R\Gamma(G_{K,S},M_i)\oplus\bigoplus_{v\in S}U_v\to\bigoplus_{v\in S}R\Gamma(K_v,M_i)\Bigr)[-1]\tag{4.3}$$
   satisfies $C_U(M_i)\simeq R\operatorname{Hom}_{R_i}(C_{U^\perp}(M_i^*(1)),R_i)[-3]$.
3. *(Support comparison.)* At a tame split prime the local free model is $d^0v=(Av,Cv)$,
   $d^1(v,w)=-Cv+Dw$ with $A=\Phi-1$, $C=g-1$, $D=\Phi-N_q(g)$, $N_q(g)=\frac{q+1}2+\frac{q-1}2g$ and
   $DC=CA$ (4.4); at $g=1$ it splits into the unramified complex and the singular quotient. Support change
   (Nekovář, Proposition 7.8.8(ii)) is used only where the coefficient representation is unramified at the
   removed place, in exactly five situations.

**Proof sketch.** (1) Local duality (Milne, I.2.3 and I.3.2–I.3.5) makes the Kummer map adjoint to
$H^1(F,B[2^a])\to H^1(F,B)[2^a]$, whose kernel is the Kummer image. The restricted cup map on
$M[-1]$, $M=B(F)^\wedge_2$, is determined by $\operatorname{Hom}(M\otimes M,\mathbb Z_2)$, and isotropy makes
every value divisible by every power of two, so it is null-homotopic; derived Nakayama lifts the comparison
from reduction mod two. At $v\mid2N$, $\Psi_i$ is trivial and every $h_x$ has the squareclasses of $h_0=1$,
so the universal character is trivial on $G_{K_v}$. (2) Conjugation acts on the ring class group by
inversion, so $\Psi_i(\tau g\tau^{-1})=\Psi_i(g)^{-1}$; with $\rho_T(\tau)^2=1$ and the Weil pairing this gives
an $R_i$-valued pairing that identifies $\tau^*M_i$ with $M_i^*(1)$. Global duality (Nekovář, Sections 5.1, 5.2.4, 5.4.3 and 6.3.4) applied to
these local maps and homotopies gives the duality. (3) The identity $DC=CA$ is a computation in the group
ring of the tame quotient; replacing the unramified by the full condition gives the singular quotient by a
cone of Selmer cones, so the old complex is an actual subcomplex of an upper triangular model.

## Depends on

- [One moving character for the complete active list](moving-character.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): the setup (L2720–2742), `ex:arith-data`
  (L2743–2760), `ex:arith-conjugate-duality` (L2761–2831), `ex:arith-local-kummer` (L3412–3469),
  support comparisons (L3470–3499)

## Manuscript check

Mapped by AI review. The proof of the integral comparison in (1) is not yet checked; only the consistency of
its cohomology with the duality was checked by script. One gap was filled. The norm $N_q(g)$ in (4.4) is the
Fox norm only when $g^2=1$, but the model is also used at the moving prime, where $g$ acts as $1+t$. It still
holds there: $DC-CA=-\frac{r-1}2(2t+t^2)$, which vanishes in $A_i$ because $r\equiv1\pmod{2^{B'}}$ with
$B'\ge n_i\ge2i$, and in the limit $N_q(g)\to1$. The review checked this by script, with a negative control.
The locators in Nekovář and Milne, and whether the local data meet Nekovář's exact hypotheses, are not yet
checked against the prints.
