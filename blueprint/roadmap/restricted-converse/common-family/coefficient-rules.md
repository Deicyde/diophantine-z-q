---
declaration: theorem
origin: cited
---

# Arithmetic realization of the coefficient rules

Take either the even source with its fixed minimum depth, or an odd source at an actual stage that satisfies the
depth inequalities through a fixed finite operator budget $|U|\le W$ (with $R\ge2$). Then the integer divisions
(O.9)–(O.11) are valid at every Fourier index (with the stated truncation for the odd source), the fresh
coefficient-one reading is $\overline{(t(\operatorname{Fr}_q)\theta H_U)[1]}=\mathcal A(Uq)$, and on all tested
nonempty configurations the symbols depend only on their typed graph and obey the following rules.

1. *(Graph dependence and whole-prime omission.)* The reading of a new vertex $q$ adjoined to a list $U$ factors
   through the elementary quadratic extension unramified outside $S\cup U$ and is determined by its type and its
   incidences with $U$. The reading after omitting $p\in U$ uses the same form, phase and depth, and is unaffected
   by inertia at the omitted prime.
2. *(Contraction.)* With $\Delta_{vw}A=A|_{z_{vw}=0}+A|_{z_{vw}=1}$, the reverse bit changing by reciprocity,
   $$\Delta_{vw}A(\Gamma)=A(\Gamma/(v,w)),$$
   where the contracted graph carries the summed type and every summed external incidence.
3. *(Primary isolation.)* A configuration containing a primary vertex neutral relative to all its other vertices
   has symbol zero.

Every contraction output is nonempty. No value is asserted at untested odd-stage weights or at an empty output.

**Proof sketch.** Put $B_U=2^{-n_U}\prod_{p\in U}(U_p-\eta(p)V_p)\,g$; $V_p$ raises the level by $p$ with character
$\psi\cdot(p/\cdot)$, and $U_{p^2}V_p=U_p$. Along shells the recurrences (E.12) and (O.6) make the successive
differences odd at $p\in U\setminus J$ and even at $p\in J$, which gives the valuation bound (O.9) and the parity
(O.10), $(b_{s+1}-b_s)/2\equiv c_p(D)\pmod2$, using $a_p\equiv p+1\pmod4$; subtracting unary theta series gives
the integral form $H_U=(B_U-\sum_JB_U[J]\Theta_J)/2$ (O.11). Multiplying by $\theta$ gives weight two, in a finite
closed integral module stable under Hecke and diamond operators and Chebotarev limits $t(g)$, $d(g)$, with
$t(1)=0$ and $t(u)t(v)=t(uv)+t(uv^{-1})$; two fresh primes give zero, so the labels are elementary quadratic. At a
new conductor-one prime the local representation is $\operatorname{Ind}(\mu_1,\mu_2)$ (Casselman), and the
Whittaker computation with Carayol's normalization gives the local identity
$U^{(2)}_p\{t(g\tau\phi)-t(g\phi)\}=d(\phi)\{t(g\tau)-t(g)\}$ (O.12). Opposite Legendre signs then give the
omission rule $\mathcal A_U(Uq_\tau)+\mathcal A_U(Uq)=\mathcal A_V(Vr_0)$, the product-label rule gives contraction,
$t(1)=0$ gives primary isolation, and a fresh-copy argument shows dependence on the typed graph only.

## Depends on

- [Compatible typed graphs and coefficient symbols](coefficient-symbols.md)

## Proof depends on

- [An actual even form with rational normalized phase](../coefficient-sources/even-form.md)
- [The actual odd theta form and its recurrence (O.6)](../coefficient-sources/odd-theta-form.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:sec7-coefficient-rules` (L2102–2150) and
  `ex:app-coefficient-rules` (L9446–9976)

## Manuscript check

Mapped by AI review and read once for structure; not yet checked line by line. The shell parities behind
(O.9)–(O.11) and the matrix identity behind (O.12) were checked by script. The statement is made on tested
nonempty configurations within a finite budget, and the odd symbol exists only as a limit of finite-stage tables;
the manuscript says explicitly that the rules are not claimed at one fixed stage for all weights, and its order of
choices (budget, then stage, then primes) is consistent. The locators of Carayol (Theorem A) and Casselman
(Theorems 1 and 4) are not yet checked against the prints.
