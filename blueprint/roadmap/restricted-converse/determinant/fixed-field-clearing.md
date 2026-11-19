---
declaration: theorem
origin: cited
---

# The fixed-field budget and a common denominator (5.6)–(5.9)

Fix the final field $K$ and a binary family over it, in the branch where the odd symbol is not a unit at the
empty configuration; there are no derivative labels, and at augmentation all graph primes are unramified. Put
$d_K=\dim_{\mathbb F_2}\mathrm{Sel}_2(E/K)$, $t_K=\operatorname{length}E(K)[2^\infty]$ and
$h_K=\operatorname{length}H^2(C_K)_{\rm tors}$.

1. *(Budget.)* The old-support subcomplex in the support triangle
   $C_{\rm old}\to(C_b)_0\to\bigoplus_{q\in Q}Q_q\to C_{\rm old}[1]$ (5.6) satisfies
   $$\operatorname{rank}_{\rm total}C_{\rm old}\le2d_K+12,\qquad m\le d_K+5,\qquad h_1\le h_K+2c_E+2t_K,\tag{5.7}$$
   with $m$ its number of Smith disks and $h_1$ the sum of their valuations, independently of the binary
   dimension and the graph. At every sign character the inverse new local blocks and the resulting Schur
   complex have no Laurent terms below $-4M$ modulo $2^M$ (5.8).
2. *(Clearing.)* With the paired-functional exponent $a$ and the correction $\eta$, there are common
   $\Delta,Q\in\mathscr O[G]$ with $\widetilde u_x=2^{-a}\eta_xQ_x/\Delta_x^3$ wherever $\Delta_x\ne0$; putting
   $f=2^a\Delta^4$ and $d=\eta\Delta Q$ gives $f_x\widetilde u_x=d_x$ at every character, $f_0\in\Lambda$, and
   $$c=v_2f_0(0)\le c_{\det}:=a+4(h_K+2c_E+2t_K),\qquad L_T(M)=16(d_K+5)M,\tag{5.9}$$
   where $L_T(M)$ bounds the negative Laurent support of every $f_x$ modulo $2^M$, uniformly in $x$.

**Proof sketch.** The graph-wide prescription of the moving character gives the scalar $1+t$ at each chosen
orientation, and the support triangle (5.6) makes $C_{\rm old}$ an actual subcomplex of an upper triangular
model. Its total rank, Smith disks and torsion are bounded by the Selmer dimension, the torsion and
$H^2(C_K)_{\rm tors}$ of the fixed field, with $c_E$ entering through the moving prime (5.7); $h_K$ is a finite
length and does not assume finiteness of all of $\mathrm{Sha}$ at the base. For a new block write
$\det A_q=t^{d_q}v_q+2w_q$ with $d_q\le4$ and $v_q$ a unit, and $C_q=\operatorname{adj}(A_q)/(t^{d_q}v_q)$; then
$B_xC=1+2F$ with $C$ and $F$ without terms below degree $-4$, and $B_x^{-1}=C\sum_{j<M}(-2F)^j$ modulo $2^M$ has
pole at most $4M$ (5.8). Block Schur and Smith operations on the old-rank complex then express $\widetilde u$
with the common denominator $\Delta^3$; $f$ is a polynomial of degree $4m$ in differential entries, each with
pole at most $4M$ at a sign character, so its pole is at most $16mM\le16(d_K+5)M$. Where $\Delta_x=0$ both $f_x$
and $d_x$ vanish and the identity holds directly.

## Depends on

- [The branch split and the nonempty seeds](../common-family/nonempty-seeds.md)
- [The paired functional and the class-functional coordinate](../heegner-limits/paired-functional.md)
- [Unused-prime comparison and the corrected coordinate (4.7)](../heegner-limits/common-coordinate.md)

## Proof depends on

- [Local conditions, the derived Kummer condition and duality](../heegner-limits/local-conditions.md)
- [One moving character for the complete active list](../heegner-limits/moving-character.md)
- [Finite free models and the inner limit](../heegner-limits/inner-limit.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:limits-fixed-field-budget` (L5207–5485) and
  `ex:limits-fixed-field-clearing` (L5486–5646)

## Manuscript check

Mapped by AI review. The arithmetic of (5.7), the pole bound (5.8) and (5.9) was checked by script. The block
Schur and Smith determinant calculus was read for structure and is not yet checked line by line. The
constants $d_K$, $t_K$ and $h_K$ are fixed only after $K$; the manuscript notes that a varying-field estimate
cannot be drawn by treating $h_K$ as an absolute constant, and none is used.
