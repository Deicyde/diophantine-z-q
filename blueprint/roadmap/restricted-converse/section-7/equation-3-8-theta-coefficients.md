---
article_id: af_3878cac255ab47d752eb7e1e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Visibility.thetaComparison_of_inputs, ZInQ.Manuscript.RC.Odd.ThetaComparison
---

# (3.8): the odd theta coefficients

For each stage $\theta$, with precision $M_\theta$, let a finite model of the weighted ternary theta
form on the definite quaternion algebra be given, with a fixed character ring $\mathscr O$, $m=|h_*|$
and $\omega=\omega(N)$. Assume, at every stage $\theta$ and admissible $D$, the inputs of the orbit
count of Appendix F (`ComparisonInputs`, named inputs, not proved): the $2^{\omega+1}$ local orientation
tuples, the parametrization of the orbits by the tuples and the class group of
$\mathbb Q(\sqrt{Dh_*})$, the weights along it, the reduction identity at the reference tuple (from
Theorem 3.1 of Cornut and Jetchev), the orientation changes, stabilizers $\{\pm1\}$, a unit phase at
the reference tuple, and an integer representative $a_\theta(D)$ of the phase-removed coefficient
modulo $2^{M_\theta}$. Let $\lambda_\theta(D)$ be the integer of the reduction identity. In the
manuscript it is a lift of $\lambda_{M_\theta}(\overline{LP^{\rm gen}_D})$; in Lean it is an arbitrary
input, constrained only by the reduction identity. Then for every stage $\theta$ and admissible $D$ there
is an odd integer $\zeta$ with
$$a_\theta(D)\equiv c_0\,2^{\omega(N)}\,\zeta\,\lambda_\theta(D)\pmod{2^{M_\theta}},\qquad
c_0=|\mathrm{GL}_4(\mathbb F_3)|=24261120.\tag{3.8}$$

Admissibility is a parameter of the statement; in the stage construction it includes the support
condition $(D/\ell_0)=1$. The Lean congruence is
for the phase-removed integer representative, so the manuscript's root-of-unity phase becomes an odd
integer; the manuscript's $c_0$ is a fixed nonzero constant. The vanishing $a_{M_\theta}(D)=0$ when
$(D/\ell_0)\ne1$ is not part of this statement.

**Proof sketch.** As in Appendix F, the coefficient at $D$ is a sum over the orbits of embeddings,
parametrized by the orientation tuples and the class group. The weights factor as a tuple phase times
a genus character, the reduction identity of Cornut–Jetchev evaluates the class-group sum at the
reference tuple, and the orientation changes compare the other tuples with it modulo $2^{M_\theta}$.
With stabilizers of order two each orbit is worth $c_0/2$, and the $2^{\omega+1}$ tuples sum to
$c_0\,2^{\omega(N)}$. No class number is divided out.

In the Lean proof of Theorem 5.3 the theta side and the comparison argument are fields of
`PreLeaves.odd_staged` in [the remaining hypotheses](../remaining-hypotheses.md); together they amount to
(3.8) itself. The same field pins the point side: there $\lambda_\theta(D)$ is the genuine reading of
the Heegner point.

## Depends on

- [(3.7): arbitrarily advanced stages](equation-3-7-advanced-stages.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
