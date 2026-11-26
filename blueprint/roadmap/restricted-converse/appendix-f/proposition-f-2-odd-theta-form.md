---
article_id: af_a8cd968ca5c42148436ea880
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.AppF.ThetaStage.oddStageCore, ZInQ.Manuscript.RC.AppF.ThetaStage.recAt, ZInQ.Manuscript.RC.AppF.ThetaStage.H, ZInQ.Manuscript.RC.Odd.OddStageCore
---

# Proposition F.2: the odd theta form and its recurrence, with (O.3)–(O.6)

Fix an actual stage of precision $M\ge2$ with detecting prime $\ell_0$, the definite quaternion algebra
$B$ ramified exactly at $\ell_0$ and $\infty$, an Eichler order of level $N$ with class set $X$ (the
supersingular pairs), $m=|h_*|$ and $c_0=|\mathrm{GL}_4(\mathbb F_3)|=24261120$. Assume a finite model
of the stage with coefficients in $\mathcal O/2^M\mathcal O$ (`ThetaStage`, named inputs, not proved):
for each class $z$ the order $w_z=|R_z^\times|$, which divides $c_0$, a value $P(z)$ standing for
$P_M(z)=\lambda_M(L\pi_{\ell_0}(z))$, the value $\chi_{h_*}(\mathrm{Nrd}\,z)$ and the theta sums
$\theta_z(n)$ with the local weights folded in, vanishing at $n=0$; the good primes $p$ with $a_p$; the
character $\eta=\eta_B\chi_{h_*}$; and the $p+1$ neighbours of each class. In Lean $P$ is not tied to
$\lambda_M$: only the eigenrelation below constrains it. Three of its fields are facts
the manuscript uses without a print: $P_M$ is a $T_p$-eigenfunction with eigenvalue $a_p$, the neighbour
counts are self-adjoint for the weights $w_z$, and the theta coefficients of a neighbour are the
$y/p$-sum, with the norm character changed by $\chi_{h_*}(p)$. The field `frame_scale` says that
scaling by $p$ at all other places multiplies the weight by $\eta_B(p)$. Assume also
$a_p\equiv p+1\pmod4$ at the good primes, which is proved for the actual curves
(`ap_mod_four_curve`), and that the coefficients vanish at indices not prime to the coefficient
support and at squarefree parameters off the stage support (ELLIOT). Put
$$H_M(n)=\sum_{z\in X}\frac{c_0}{w_z}\,P(z)\,\chi_{h_*}(\mathrm{Nrd}\,z)\,\theta_z(n),\qquad
a_M(n)=H_M(mn).\tag{O.4}$$
Then $a_M(0)=0$, and at every good prime $p$ and every index $n$, with $\psi(p)=\eta(p)(-1/p)$, that is
$\psi/\eta=\chi_{-1}$, and $a_M(n/p^2)=0$ when $p^2\nmid n$,
$$a_M(p^2n)\equiv\{\eta(p)a_p-\psi(p)(-n/p)\}\,a_M(n)-p\,\eta(p)^2a_M(n/p^2)\pmod{2^M\mathcal O}.
\tag{O.6}$$

The Lean statement is the coefficient form in which an odd stage source is used (`OddStageCore`, which
asks only that $(\psi/\eta)(p)$ be a sign; `recAt` gives $(-1/p)$). It does not state that
$g_M=\sum a_M(n)q^n$ is a holomorphic form of weight $3/2$, its level, or $\psi=\eta_B(m/\cdot)$. The
existence of a `ThetaStage` for the actual stage (quaternion orders, the adelic class set, the local
identifications) is not formalized. The description of the class set is cited from Jetchev and
Kane, who assume $N>1$; for Theorem 5.3, $N$ is the conductor of $E_\ell$, so $N>1$.

The merged displays: (O.3), the condition $\alpha_p(-1)=w_{p^e}\chi_{h_*}(p)^e$ on the local weight
characters at $p^e\Vert N$, has no Lean statement; its purpose, $\alpha(-1)=1$ for the global scaling
character, is `Odd.alpha_neg_one`, from the local signs, the Atkin–Lehner sign of $E$ and the twist
formula for the root number (GLUE), and $w(E^{(h_*)})=+1$. The Weil-index steps are finite algebra over
axioms for the Weil index and the Hilbert symbol: (O.5a) is `Visibility.O5a_ternary`, (O.5c) is
`Visibility.O5c` and (O.5) is `Visibility.extracted_character`; (O.5b) appears only as the character
$a\mapsto\alpha(a)(a,\det Q)$ (`Visibility.eigenCharacter`), not as an eigenvalue of the theta
multiplier. None of these is an input of the theorem.

This theorem is not on the path of the reduction of Theorem 5.3. There the theta side is a field of
`PreLeaves.odd_staged` in [the remaining hypotheses](../remaining-hypotheses.md), over a separate finite
model of (O.4) (`Visibility.ThetaStage`, with the sum `Visibility.thetaCoeff`), and the odd stage
source is read through the trace models of `PostLeaves.address`. The two models are identified only
through `ThetaCoeff.Lift`, which pairs an `AppF.ThetaStage` with a `Visibility.ThetaStage` and reduces
`thetaCoeff` to `ThetaStage.H` (`Lift.H_reduce`); the reduction does not use it, and its theta side
carries no `Lift`. In the reduction (O.6) and (O.7) therefore concern unrelated models.

**Proof sketch.** At a good prime $p$, with $s=\eta_B(p)$, summing the neighbour identity of the theta
sums over the $p+1$ neighbours, moving the neighbour operator across by self-adjointness and using the
Hecke eigenrelation of $P_M$ gives the Brandt identity
$H_M(p^2n)+s(-n/p)H_M(n)+ps^2H_M(n/p^2)=s\chi_{h_*}(p)a_pH_M(n)$ at every index. At the indices $mn$,
$(-mn/p)=(m/p)(-n/p)$ and $(m/p)=(-1/p)\chi_{h_*}(p)$, which gives (O.6). The coefficient at $0$ is zero
since every $\theta_z(0)$ is.

## Depends on

- [(3.7): arbitrarily advanced stages](../section-7/equation-3-7-advanced-stages.md)

## Sources

- [Appendix F](../../../sources/manuscript.md#appendix-f)
