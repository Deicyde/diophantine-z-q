---
article_id: af_ab3f718c58ed103aa809bfce
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.HalfIntegral.evenPhaseData_Ecurve, ZInQ.Manuscript.RC.Even.EvenPhaseData.E11, ZInQ.Manuscript.RC.Even.EvenPhaseData.minimum_sieved, ZInQ.Manuscript.RC.Even.EvenPhaseData, ZInQ.Manuscript.RC.AppE.evenPhaseData_of_prints
---

# (E.11): the actual even form and its rational phase

Assume Waldspurger's nonvanishing theorem together with the manuscript's local construction of a form
with scalar character (`WaldspurgerNonvanishing`, ELLIOT: Waldspurger's theta theorem, print unverified,
with the manuscript's own passage to a classical form with scalar character of two-power order and
level supported on $S_0$), Waldspurger's Corollaire 2 (`WaldspurgerCor2`, GLUE: restated from
Purkait's Corollary 5.2, print unread; see [(E.10)](equation-e10-waldspurger-ratio.md)) and Ramsey's
algebraic model of the weight $3/2$ spaces (`RamseyAlgebraicModel`, GLUE: Ramsey's printed form as
the manuscript uses it, locators unverified, with the manuscript's flat-base-change check and an
integral-weight Galois action the manuscript does not cite); none of the three is an input of the
reduction of Theorem 5.3. Assume also modularity in newform form
(`ModularNewform`, which follows from [the cited results](../printed-results.md) and three fields of
[the remaining hypotheses](../remaining-hypotheses.md), `RCLeaves.modularNewform`) and, for the
minimum, [(E.9)](equation-e9-lower-bound.md). The absolute convergence of $L(E,s)$ on
$\operatorname{Re}s>3/2$ and the twisting step for weight $3/2$ forms, also hypotheses of the Lean
theorems, are proved.

Let $\ell>0$, $E=E_\ell$ with a normalization $L_*$, $\sigma=\pm1$, $S_0$ the primes dividing $2N_E$, where
$N_E$ is the level of the functional equation of $L(E,s)$ (the conductor), and $D_0>0$ squarefree, prime
to $S_0$, with $L_*(\sigma D_0)\ne0$. Then there are a
level $N$ with $4\mid N$ and prime factors in $S_0$, characters $\psi$ and $\eta=\psi\chi_{-\sigma}$
modulo $N$, and a cusp form $g$ of weight $3/2$, level $N$ and character $\psi$ in the good-Hecke
eigenspace of $E$ and $\eta$, with $a_g(D_0)\ne0$, such that every $D$ in the $S_0$-filter of $D_0$ satisfies,
for $a(D)=a_g(D)/a_g(D_0)$,
$$a(D)=z_Dr_D,\qquad z_D\in\mu_{2^\infty},\quad r_D\in\mathbb Q,\qquad r_D^2=\frac{L_*(\sigma D)}{L_*(\sigma D_0)}.\tag{E.11}$$
Moreover, for every finite set $B$ of primes prime to $D_0$, the values $v_2r_D-\omega(D)$ at the $D$ of
the filter prime to $B$ with $r_D\ne0$ have an attained minimum.

Proposition E.4 has no single Lean statement: its form, (E.11) and its minimum are on this page, and
its recurrence is [(E.12)](equation-e12-hecke-recurrence.md). Lean divides by $a_g(D_0)$ instead of
normalizing $a(D_0)=1$, and $v_2a(D)=v_2r_D$ because $z_D$ is a root of unity. The form does not depend
on $B$; the sieve by $B$ is applied to the indices of the minimum, not to the form. A second Lean theorem
gives the same data for any elliptic curve and any finite $S_0\ni2$ containing the conductor primes.

**Proof sketch.** Modularity turns $L_*(\sigma D_0)\ne0$ into analytic rank zero, and the nonvanishing
theorem with the local construction gives $N$, $\psi$, $\eta$ and $g$. The phase $z_D$ is $\eta$ at a square
root of $D/D_0$ modulo the level, a two-power root of unity with $z_D^2=\psi(D)\psi(D_0)^{-1}$. Ramsey's
model, the twisting step and the proportionality given by Corollaire 2 show that $a(D)/z_D$ is fixed by
every automorphism of $\overline{\mathbb Q}$, hence rational. Then (E.10) gives $r_D^2$. For the minimum,
(E.9) at the odd squarefree parameter $\sigma D$ bounds $v_2r_D-\omega(D)$ below, and $D_0$ makes the set
nonempty.

In the Lean proof of Theorem 5.3 this theorem is not used: the field `PreLeaves.even_upper` asks
directly for [(3.3a)](../section-7/equation-3-3a-unit-symbol-bound.md), which the manuscript derives
from this form. The field `PostLeaves.address` (ELLIOT and GLUE) contains, in `AddressDensityLeaf`, the
clause `EvenReading` (ELLIOT): (F.1)'s conclusion for the final companion's transported even source,
which the manuscript reads from (E.11).

## Depends on

- [The cited results](../printed-results.md)
- [The remaining hypotheses](../remaining-hypotheses.md)
- [Appendix E: the filter of a reference index](README.md)

## Proof depends on

- [(E.10): Waldspurger's ratio of squared coefficients](equation-e10-waldspurger-ratio.md)
- [(E.9): the lower bound for $v_2L_*$](equation-e9-lower-bound.md)

## Sources

- [Appendix E](../../../sources/manuscript.md#appendix-e)
