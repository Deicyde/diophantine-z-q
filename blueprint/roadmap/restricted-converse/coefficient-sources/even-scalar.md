---
declaration: theorem
origin: cited
---

# The fixed-form even scalar (3.2)

Put $\Lambda=\mathbb Z_2[[t]]$, for the real cyclotomic $\mathbb Z_2$-extension, and
$\mathscr O=\widehat{\Lambda_{(2)}}$. Let $G$ be a finite elementary abelian two-group and
$\chi_x=\chi_0(x\circ\varepsilon)$, $x\in\widehat G$, a family of quadratic characters with one real sign
and the same restrictions at every place dividing $2N$. There is one scalar
$u^{\rm ev}\in\Lambda[1/2][G]$ with
$$2^{C_{\rm ev}}u^{\rm ev}\in\Lambda[G],\qquad v_2u^{\rm ev}_h(0)=v_2L_*(h)-2\omega(h)-s(h)+O_E(1)\tag{3.2}$$
at every constituent $h$ of Selmer corank zero with $L_*(h)\ne0$. The exponent $C_{\rm ev}$ and the bounded term
depend only on the fixed data, not on $G$ or on the good primes of the conductors. At a corank-zero
constituent, $u^{\rm ev}_h(0)=0$ exactly when $L_*(h)=0$. Consequently, with $G=1$, every admissible $h$ with
$L_*(h)\ne0$ satisfies
$$v_2L_*(h)\ge2\omega(h)+s(h)-c_E-C_{\rm loc}.\tag{E.9}$$

**Proof sketch.** Appendix E builds one retained-smoothed Kato class $Z_F$ for the whole family, with
height-one divisibility (K2) and central reciprocity (K3). The positive complex $C^+$, the fibre of the
ordinary global cochains to the real cochains, has finite free models by the nilpotent perturbation of
Section 9. In the real cyclotomic tower the two-class group vanishes: only the prime above two ramifies in
each quadratic step. A unit of norm $-1$ makes the signatures span, so the residual dimensions are
$\dim H^1=2^n+s_n-1$ and $\dim H^2=s_n-1$, and $C^+\otimes\mathscr O[G]\simeq\mathscr O[G]^2[-1]$ (E.3).
Wedging a generator $a$ of the real invariant lattice with a lift of $2^{c_E+1}F_EZ_F$ gives
$u^{\rm ev}$ (E.4). By (K2) its valuation at each height-one prime is a nonnegative length difference, so
$u^{\rm ev}\in\Lambda[1/2][G]$, and with (E.3) $2^{c_E}u^{\rm ev}\in\Lambda[G]$ (E.5). At a corank-zero
constituent, the Kummer duality length formula gives
$v_2u(0)=v_2\exp^*z-s-\sum_vg_v+2g+1-r_1-e_2$ (E.6)–(E.7). The unused-prime terms
$v_2\#E^h(\mathbb F_q)$ of (K3) cancel against the $g_q$, and each active good odd prime has $g_v=2$ because
its inertia invariants are all of $E[2]$, which gives $-2\omega(h)$ (E.8). The forward rank-zero case of
Lemma 5.5 supplies corank zero and finite $\mathrm{Sha}$ when $L_*(h)\ne0$, which gives (E.9).

## Depends on

None.

## Proof depends on

- [One retained Kato system (K1)–(K3)](kato-system.md)
- [Finite free models and the inner limit](../heegner-limits/inner-limit.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:sec7-even-scalar` (L1832–1966), with
  `ex:app-even-scalar` (L7367–7612) and `ex:app-central-calibration` (L7613–7787)

## Manuscript check

Mapped by AI review; the appendix construction was read once for structure and is not yet checked line
by line. Spot checks by script: the smoothing constants give $v_2s_F=2e$, and the count of negative
conjugates of the unit $1+\zeta+\zeta^{-1}$ is odd for every layer up to $m=15$. The term $-2\omega(h)$
comes from the length-two inertia invariants $E[2]$ at the active primes, the count that the later
comparisons need. The
Kato locators are not yet checked against the print.
