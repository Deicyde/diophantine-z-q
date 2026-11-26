---
article_id: af_f2c4f6ab3f5a8b9f05afd085
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Visibility.ComparisonCore.O7, ZInQ.Manuscript.RC.Visibility.O7_of_inputs, ZInQ.Manuscript.RC.Visibility.ComparisonCore
---

# Proposition F.3: the unaveraged theta comparison (O.7)

Fix a stage of precision $M$ with detecting prime $\ell_0$, the coefficient ring $\mathcal O$,
$m=|h_*|$, $\omega=\omega(N)$, and a positive squarefree $D$ in the odd filter with $(D/\ell_0)=1$, so
that $\ell_0$ is inert in $F=\mathbb Q(\sqrt{Dh_*})$; this is the manuscript's setting, and in Lean $m$
and $D$ are arbitrary integers. Let a finite model of (O.4) be given (`Visibility.ThetaStage`, the
model of the reduction's theta side, not the `AppF.ThetaStage` of
[Proposition F.2](proposition-f-2-odd-theta-form.md)), over the quaternion algebra
$(a,b)_{\mathbb Q}$ with arbitrary rational $a,b$, so that nothing forces it to be definite or
ramified at $\ell_0$: a finite set $X$ of classes $z$ (GLUE), unit groups $R_z^\times$ of order
dividing $c_0$ (GLUE), weights $f(z^{-1}xz)$ invariant under $R_z^\times$ (ELLIOT), the values
$\chi_{h_*}(\mathrm{Nrd}\,z)$, well defined on $X$ (ELLIOT), integers $P(z)$, arbitrary and linked to
$\lambda_M$ only by the reduction identity below, and weights of finite support on each norm sphere
(ELLIOT and GLUE). Let $\lambda$ be an integer. Assume the comparison argument at $(M,D)$
(`ComparisonCore`, named inputs, not proved):

- $2^{\omega+1}$ local orientation tuples, and a parametrization of the $R_z^\times$-orbits of the
  trace-zero $x$ with $Q_B(x)=mD$ and nonzero weight, over all classes $z$, by pairs of a tuple and a
  class of $\operatorname{Pic}(\mathcal O_F)$ (ELLIOT);
- the weights along it: a phase $\zeta_0(t)$ of the tuple times the genus character
  $\chi_F([\mathfrak a])=\chi_{h_*}(\mathrm N\mathfrak a)$ (ELLIOT);
- at the reference tuple $t_0$, the reduction identity
  $\sum_{c}\chi_F(c)P(z_{t_0,c})\equiv\lambda\pmod{2^M}$ (PRINT and ELLIOT: Theorem 3.1 of Cornut and
  Jetchev, a printed result that is not one of [the cited results](../printed-results.md), with
  Elliot's argument);
- the orientation changes: after its phase, the class-group sum of each tuple is congruent to that of
  $t_0$ modulo $2^M$ (ELLIOT);
- stabilizers of order two (ELLIOT and GLUE);
- $\zeta=\zeta_0(t_0)$.

Then, with $c_0=|\mathrm{GL}_4(\mathbb F_3)|$,
$$H_M(mD)\equiv c_0\,2^{\omega(N)}\,\zeta\,\lambda\pmod{2^M\mathcal O}.\tag{O.7}$$

In the manuscript $\lambda$ is $\lambda_M(\overline{LP_D})$, with $P_D$ the point
[(O.1)](equation-o-1-genus-point.md), and $\zeta$ is a $2$-power root of unity in the field of the
characters at the primes of $N$; the Lean phase is the reference tuple's, with no condition, and the
theta side of the reduction asks only that it be a unit. The condition $(D/\ell_0)=1$ is not a
hypothesis; it enters through the orbit parametrization.

In the reduction of Theorem 5.3 the comparison argument at every admissible $(\theta,D)$ is a field of
the odd models in `PreLeaves.odd_staged` of [the remaining hypotheses](../remaining-hypotheses.md),
with $\lambda$ the integer lift `lamOf` of $\lambda_{M_\theta}(\overline{LP_D})$, and (O.7) is this
theorem; with the phase removed by the theta side's integer representative it is
[(3.8)](../section-7/equation-3-8-theta-coefficients.md) (`thetaComparison_of_core`). Since the theta
side and the comparison argument exist for every $\lambda$ with
$a_\theta(D)\equiv c_0\lambda\pmod{2^{M_\theta}}$ (the docstring of `PreLeaves.odd_staged`), together
they amount to (O.7) itself. The theta side's models are `Visibility.ThetaStage`s; they are identified
with the `AppF.ThetaStage` of Proposition F.2 only through `ThetaCoeff.Lift` (`Lift.H_reduce`), which
the reduction does not use. In the reduction (O.6) and (O.7) therefore concern unrelated models.

**Proof sketch.** Group the sum over $x$ at each class into $R_z^\times$-orbits: with stabilizers of
order two each orbit carries the integer $c_0/2$. Reindex the orbits by tuples and classes and insert
the weights. The reference tuple's class-group sum is $\lambda$ modulo $2^M$ by the reduction identity,
and each other tuple's sum, after its phase, is congruent to it. The $2^{\omega+1}$ tuples, each worth
$c_0/2$, give $c_0\,2^{\omega(N)}$; no class number is divided out.

## Depends on

- [(O.1): the conductor-one point](equation-o-1-genus-point.md)
- [Proposition F.2: the odd theta form, with (O.4)](proposition-f-2-odd-theta-form.md)

## Sources

- [Appendix F](../../../sources/manuscript.md#appendix-f)
