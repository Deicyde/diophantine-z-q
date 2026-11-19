---
declaration: theorem
origin: cited
---

# Finite coefficient transfer and the final contradiction

Use the fixed field $K=\mathbb Q(\sqrt k)$, the common family $h_x$ of (3.9), the regular corrected coordinates
$\widetilde u_x$ and the integral identity $f_x\widetilde u_x=d_x$ of the fixed-field clearing. Let $B$ be the
upper bound on $v_2\widetilde u_x(0)$ at every nonzero address supplied by (3.9), (3.4), (4.6) and (4.7), fixed
before $b$, and choose
$$M>\max(c_{\det},B+2c_{\det}),\qquad b>(L_T(M)+2)(2^M-1),\tag{5.10}$$
before the finite graph and its theta stage are realized. Then for some nonzero address $x$,
$$v_2\bigl(\widetilde u_x(0)-\widetilde u_0(0)\bigr)\ge M-2c>B,\qquad c=v_2f_0(0)\le c_{\det}.\tag{5.11}$$
If $L'(E/K,1)=0$, the base lemma makes $\widetilde u_0(0)=0$, contradicting the upper bound at $x$. Since
$L(E^{(k)},1)\ne0$, it follows that $\operatorname{ord}_{s=1}L(E,s)=1$.

**Proof sketch.** At a nonzero address the central identity (F.8),
$v_2\widetilde u_x(0)=2j_{\rm rc}(h_x,k)-4\omega(h_x)-s(h_x)-s(h_xk)-\sum_{p\mid k}t_p+\epsilon'_x$, together with
$2j_{\rm rc}(h_x,k)\le4\omega(h_x)+C_J$ and the nonnegative $\mathrm{Sha}$ terms, gives $v_2\widetilde u_x(0)\le B$.
Apply the Boolean-degree lemma to the coefficients of $f$ from $t^{-L_T(M)}$ through $t^0$ and to the constant
coefficient of $d$: by (5.10) their degrees sum to less than $b$, so some $x\ne0$ agrees with the base in all of
them modulo $2^M$. There the negative coefficients of $f_x$ vanish modulo $2^M$ and its constant term has
valuation $c$, so $v_{\mathscr O}(f_x)\le c$ and $v_{\mathscr O}(\widetilde u_x)\ge-c$. Both $\widetilde u_x$ and
$\widetilde u_0$ lie in $\Lambda[1/2]$ by height-one regularity. Writing $F_x=[t^0]f_x$, the convolution
$[t^0]d_x=F_x\widetilde u_x(0)+E_x$ has $v_2E_x\ge M-c$, and
$F_x(\widetilde u_x(0)-\widetilde u_0(0))=([t^0]d_x-[t^0]d_0)-(F_x-F_0)\widetilde u_0(0)-E_x$ has every term of
valuation at least $M-c$, with $v_2F_x=c$; this is (5.11). Finally $L(E/K,s)=L(E,s)L(E^{(k)},s)$.

## Depends on

- [The fixed-field budget and a common denominator (5.6)–(5.9)](fixed-field-clearing.md)
- [One family for the two coefficient tests (3.9)](../common-family/final-family.md)

## Proof depends on

- [Bit degrees of sign-value functions and cube parity](../common-family/boolean-degree.md)
- [The unknown base has zero coordinate if its derivative vanishes](../heegner-limits/base-zero.md)
- [Central specialization and arithmetic calibration (4.5), (4.6)](../heegner-limits/central-calibration.md)
- [Unused-prime comparison and the corrected coordinate (4.7)](../heegner-limits/common-coordinate.md)
- [The genus bound before odd normalization (3.4)–(3.6)](../common-family/genus-lower-bound.md)
- [Uniform ring lower bound and height-one regularity (5.5)](../heegner-limits/uniform-lower-bound.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:limits-coefficient-transfer` (L5647–5739), and
  its restatement with (F.8) in Appendix G (L10862–10935)

## Manuscript check

Checked by AI review. The choice (5.10), the cube parity and the Boolean degrees were checked by script; the
convolution estimate (5.11) was checked by hand: $E_x$ has valuation at least $M-c$, $F_x$ has valuation $c$,
and $M>B+2c_{\det}$, with $B$ fixed before $b$ (it depends on $C_o$, $C_e$, $C_J$ and the bounded term in (4.6)). The
closing step from $L'(E/K,1)\ne0$ and $L(E^{(k)},1)\ne0$ to a simple zero was checked. The restatement at
L10862–10935 uses the same constants. The upper bound $B$ rests on the upper use of (3.4), and so on the form of
Cai–Shu–Tian's Theorem 1.1 discussed there, which is not yet checked against the print.
