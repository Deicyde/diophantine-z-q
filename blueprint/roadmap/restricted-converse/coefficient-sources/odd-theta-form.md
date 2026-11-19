---
declaration: theorem
origin: cited
---

# The actual odd theta form and its recurrence (O.6)

Fix an actual stage of the detecting sequence with $M\ge2$. Use $m=|h_*|$, the fixed multiplier $L$, the
Eichler order of level $N$ in the quaternion algebra $B$ ramified exactly at $\ell_0$ and $\infty$, the function
$P_M(z)=\lambda_M(L\pi_{\ell_0}(z))$ on supersingular points, and the local Schwartz functions of the
appendix, including the root characters $\alpha_p$ at $p\mid N$ with
$$\alpha_p(-1)=w_{p^e}\,\chi_{h_*}(p)^e.\tag{O.3}$$
With $c_0=|\mathrm{GL}_4(\mathbb F_3)|=24\,261\,120$, the weighted theta sum $H_M$ (O.4) is well defined modulo
$2^M$ in the character ring and gives an actual holomorphic form
$$g_M=\sum_na_M(n)q^n,\qquad a_M(n)=H_M(mn),\qquad g_M\in M_{3/2}(\Gamma_0(K),\psi),$$
with level supported only at the specified coefficient primes and characters $\psi=\eta_B(m/\cdot)$,
$\eta=\eta_B\chi_{h_*}$, so that $\psi/\eta=\chi_{-1}$. For every prime $p$ outside that support and every index,
$$a_M(p^2n)=\{\eta(p)a_p(E)-\psi(p)(-n/p)\}a_M(n)-p\,\eta(p)^2a_M(n/p^2)\pmod{2^M\mathcal O},\tag{O.6}$$
with nonintegral indices read as zero. Changing the lifts of $P_M$ loses no precision, and a further local
coefficient sieve keeps these conclusions outside the enlarged support.

**Proof sketch.** At the stage, Frobenius squared is trivial on $E[2^M]$, and $\kappa_M$ identifies
$E(\mathbb F_{\ell_0^2})/2^M$ with $E[2^M]$. The function $P_M$ has Hecke eigenvalues $a_p$, Atkin–Lehner
eigenvalues $w_{p^e}$ once $L$ kills the cuspidal term, and eigenvalue $+1$ for the uniformizer at $\ell_0$. The
local weights are: root projectors at $p\mid N$ (integral spectral projectors of $(1+x)/2$ at $2$), a nilpotent
sign at $p\mid m$, and the residue-line character $(t/\ell_0)$ at $\ell_0$. Their product has
$\alpha(-1)=w(E^{(h_*)})=+1$. Unit groups $R_z^\times$ embed in $\mathrm{GL}_4(\mathbb Z)$ and inject modulo $3$, so
$|R_z^\times|$ divides $c_0$, and $v_2c_0=9$. The transformation law comes from the Weil representation: the
Weil-index identity $\gamma(ua)/\gamma(a)=(\gamma(u)/\gamma(1))(u,a)_p$ for the quaternion norm form, the
operators of the double cover, the eigenvalue quotient $\alpha_p(a)(a,\det Q)_p$ (O.5a)–(O.5b), reciprocity
(O.5c), holomorphy at the cusps, and extraction by the form $Q_B/m$ (O.5). For the recurrence, a nonzero split
or irreducible reduction has $1+(-n/p)$ invariant lines, a nonzero nilpotent one, and zero $p+1$; the unique
integral nilpotent neighbour gives the remaining term, and self-adjointness of the neighbour matrix moves the
operator onto $P_M$, giving $\chi_{h_*}(p)a_pH(n)$ and so (O.6).

## Depends on

- [One witness and a compatible detecting sequence (3.7), (O.2)](odd-witness.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:app-theta-form` (L8408–9100)

## Manuscript check

Checked line by line by AI review, as part of a check of L8408–9405 with 101 checks by script, every script with
negative controls: $c_0$ and $v_2c_0=9$, all local weights and their conjugation and scaling laws, (O.3) and
$\alpha(-1)=1$, the Weil-index calculus (O.5a)–(O.5c) at $v=2,3,5,7,\infty$, the extracted characters, the local
counts behind (O.6), and a global model of (O.4) and (O.6) on a definite algebra of class number one, where the
recurrence holds on 1,617 pairs $(p,n)$ per case. Two gaps were filled. The step moving the neighbour operator
onto $P_M$ (L9067–9081) is written in two sentences; written out it uses $N_{ij}/w_i=N_{ji}/w_j$, the change of the
genus character by $\chi_{h_*}(p)$ across a neighbour, and $\sum_iN_{ji}P(i)=a_pP(j)$. In the formula for
$\alpha(-1)$ (L8579–8592) the final factor $-1$ is $(-1/\ell_0)$, which is $-1$ because $\ell_0\equiv-1\pmod{2^M}$.
Not yet checked: Weil's Theorem 6 of Part III and I.14 (whose identities were checked numerically), Voight's Main
Theorem 14.6.1 and Jetchev–Kane against the prints; three structural steps (holomorphy at the cusps, uniqueness of
the normal form for the double cover, the lower-unipotent depth) were read only; and the Hecke and Atkin–Lehner
compatibility of supersingular reduction is used as a standard fact without a print. TeX comments before the
appendix's subsections (L8222–8223, L8407) are editorial notes from the file's assembly.
