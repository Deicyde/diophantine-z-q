---
declaration: theorem
origin: cited
---

# The opening reduction

Let $\ell\equiv11\pmod{12}$ be positive and squarefree and $E=E_\ell:y^2=x(x-\ell)(x+3\ell)$. Then
$c_4=208\ell^2$, $\Delta=2304\ell^6$ and $j=35152/9$, so $E$ has full rational two-torsion, with roots
$0,\ell,-3\ell$, and no complex multiplication. The curve is modular: there are a rational weight-two
newform $f$ of level $N$, an elliptic quotient $q_f:J_0(N)\to A_f$ in the rational isogeny class of $E$, and
a rational isogeny $\alpha:A_f\to E$, so that $\varphi=\alpha q_f$ and $\pi(x)=\varphi([x]-[\infty])$ satisfy
$\pi(\infty)=0$ and $\varphi T_q=[a_q(f)]\varphi$ for $q\nmid N$. If
$\operatorname{corank}_{\mathbb Z_2}\mathrm{Sel}_{2^\infty}(E/\mathbb Q)=1$, the root number of $E$ is $-1$;
hence $\operatorname{ord}_{s=1}L(E,s)$ is odd, and Theorem 5.3 amounts to excluding analytic rank three or
more.

The rest of the proof follows the manuscript's dependency order: (a) a fixed-form Euler-system calculation
gives the even coefficient bound; (b) a varying-companion arithmetic estimate, proved by the two limits of
Section 9, gives (c) the genus-point lower bound; (d) only after that are the odd coefficients normalized,
and their finite-stage forms and the even forms give one common binary family; (e) a fixed-field
determinant argument excludes a zero derivative at the base. The even estimate does not use (e).

**Proof sketch.** The invariants are computed from the Weierstrass coefficients, and a rational CM
$j$-invariant is an integer. Modularity is Theorem A of Breuil–Conrad–Diamond–Taylor, and the modular
quotient is Milne's Theorem 11.19 with Remark 11.18. Quotienting by a rational point of order two gives a
rational two-isogeny, so the Selmer parity theorem of Dokchitser–Dokchitser (Theorem 1.8) applies: corank
one is odd, so the root number is $-1$. This uses neither Mordell–Weil rank nor finiteness of
$\mathrm{Sha}$. The congruence on $\ell$ only records where Theorem 5.3 is applied: in Section 5.1 both
parameters lie in this class and have 2-Selmer dimension three, hence corank one by Lemma 5.4 (remark
`ex:sec7-rc-scope`).

## Depends on

None.

## Sources

- [The 11/5 manuscript](../../sources/manuscript.md): `sec:rc` opening (L1760–1796), remark
  `ex:sec7-rc-scope` (L1797–1814), the dependency order (L1816–1823)

## Manuscript check

Checked by AI review step by step to L1823. The invariants, the full two-torsion and the non-integrality
of $j$ were checked by script for nine values of $\ell$, and $\ell\equiv3\pmod4$ as well. The use of
Lemma 5.4 in the scope remark was checked. The locators of Breuil–Conrad–Diamond–Taylor (Theorem A and
"conditions (1)–(6)"), Milne (Theorem 11.19, Remark 11.18) and Dokchitser–Dokchitser (Theorem 1.8) are not
yet checked against the prints. The outline at L1816–1823 does not mention the branch in which the odd
symbol is a unit at the empty configuration, where Theorem 5.3 follows from (O.8) at $D=1$ without the
determinant argument (L2584–2594). It also does not say where the Selmer hypothesis enters: only in the
root number (L1792–1796) and in $s_2(E/K)=1$ for the companion field (L2616–2626), which feeds the base
lemma and the fixed-field budget. With these two additions the outline matches the proof, and there is no
circularity: from Section 9 the even upper bound uses only the Boolean-degree lemma, which is
self-contained.
