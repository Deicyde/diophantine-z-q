---
article_id: af_7cac67080ae6aebfdc9de96d
---

# Appendix E: the even coefficient source

Appendix E builds the even side of the proof of [Theorem 5.3](../restricted-converse.md). From Kato's
Euler system for $E$ at the prime $2$ it constructs one retained class for each binary family of
quadratic twists, with a height-one divisibility and a central reciprocity law (Proposition E.1). It
places that class in a positive complex and extracts one scalar $u^{\rm ev}$ with a clearing exponent
independent of the family (Proposition E.2), and it compares $v_2u^{\rm ev}_h(0)$ with
$v_2L_*(h)-2\omega(h)-s(h)$ up to a bounded error, which gives a lower bound for $v_2L_*$
(Proposition E.3). Together these prove [Proposition 7.2](../section-7/proposition-7-2-even-scalar.md).
Finally it produces an actual weight $3/2$ form whose coefficients have rational normalized phase,
obey the good Hecke recurrence and attain a minimum of $v_2a(D)-\omega(D)$ (Proposition E.4); Section 7
and Appendix G read the even coefficient symbol from this form.

In Lean, Propositions E.1–E.3 are one step, `AppEFromKato` (the manuscript's own step, not proved):
from Kato's zeta elements it gives `AppEOutputs`, which fixes the constants and then, for every
admissible binary family, provides (`EvenFamilyOutput`) a scalar by its group-basis coefficients, the
membership of each constituent in $\Lambda[1/2]$ (`charEval_mem`), the membership of $2^{c_E}u^{\rm ev}$ in
$\mathscr O[G]$ (`outer`), the data of [(E.8)](equation-e8-central-calibration.md) at each corank-zero
constituent with $L_*(h)\ne0$, tied to the central value of the scalar, to $v_2L_*(h)$ and to $s(h)$
(`const`), and the criterion $u_h(0)=0\iff L_*(h)=0$ at corank zero (`zero_iff`). The Lean proof of
Proposition 7.2 derives (3.2) from these outputs. Proposition E.4's form is the structure
`EvenPhaseData`, which a Lean theorem constructs from modularity, Waldspurger's nonvanishing theorem
with the manuscript's local construction (ELLIOT), his Corollaire 2 as restated by Purkait (GLUE) and
Ramsey's algebraic model as the manuscript uses it (GLUE); see [(E.11)](equation-e11-rational-phase.md).

## Definitions

**The rings.** $E/\mathbb Q$ has no complex multiplication and conductor $N$, $T=T_2E$,
$\Lambda=\mathbb Z_2[[t]]$ is the Iwasawa algebra of the real cyclotomic $\mathbb Z_2$-extension,
$A=\Lambda[1/2]$, and $\mathscr O$ is the completion of $\Lambda$ localized at $(2)$. In Lean, $\Lambda$
and $A$ are the power series over $\mathbb Q_2$ with integral coefficients (`InLam`) and with bounded
denominators (`InLamHalf`), and an element of $A[G]$ or $\Lambda[G]$ is its family of group-basis
coefficients.

**Binary families.** For a finite elementary abelian $2$-group $G$, the characters
$\chi_x=\chi_0(x\circ\psi)$, $x\in\widehat G$, are quadratic characters $\chi_{h_x}$ of odd squarefree
parameters with one sign and the same squareclasses at the primes dividing $2N$, and
$h_{x+y}h_xh_yh_0$ is a square; $F$ is the squarefree product of the primes dividing some $h_x$. A prime
of $F$ not dividing $h$ is *unused* for $h$; it is good, since the family has the same local
characters at the bad primes. In Lean these are `BinaryFamily`, `BinaryFamily.support` and
`unused_disjoint_fixed`.

**Normalized central values.** With fixed periods, $L_*(h)=\sqrt{|h|}\,L(E^{(h)},1)/|\Omega^{\operatorname{sign}h}|$
is rational (Birch and Manin), $s(h)$ is the length of $Ш(E^{(h)}/\mathbb Q)[2^\infty]$, and corank zero
means $\operatorname{corank}_{\mathbb Z_2}\mathrm{Sel}_{2^\infty}(E^{(h)}/\mathbb Q)=0$. In Lean these are
`CentralNormalization`, `shaLen` and `CorankZero`.

**The positive complex and the scalar.** $C^+$ is the fibre of the ordinary global cochains to the
ordinary real cochains, real degree zero retained. For $B=\mathscr O[G]$ one has
$C^+\otimes B\simeq B^2[-1]$ (E.3), and $u^{\rm ev}\theta=2^{-c_E}a\wedge b$ (E.4), where $\theta$ is a basis of
the inverse determinant line, $a$ the connecting class of a real invariant generator and $b$ a positive
lift of $2^{c_E+1}F_EZ_F$. Neither display is stated in Lean. Proved supporting algebra: a minimal free
model has zero residual differential (`minimal_residue_eq_zero`), twice a class has a positive lift
(`exists_lift_two_smul`), the wedge does not depend on the lift (`wedge_lift_indep`), and
$2^{-c_E}a\wedge b=2a\wedge\widetilde z$ (`E4_eq_two_wedge`).

**The filter of a reference index.** For a finite set $S_0\ni2$ of primes containing the bad primes and
$D_0>0$ squarefree and prime to $S_0$, the $S_0$-filter of $D_0$ consists of the squarefree $D>0$ prime
to $S_0$ in the unit squareclasses of $D_0$ at every $p\in S_0$. In Lean this is `S0Filter`, proved
infinite.

## The items

- [(K5)–(K6): the retained smoothing and its central scalar](equation-k6-smoothing-scalar.md)
- [(K7): the Mackey formula for restriction of a corestriction](equation-k7-mackey-formula.md)
- [(K10) and (E.2): the coefficient maps on group bases](equation-k10-coefficient-map.md)
- [(E.1): the constituent identity at finite level](equation-e1-finite-identity.md)
- [(E.4a): the height-one valuations of the even scalar](equation-e4a-height-one-valuations.md)
- [(E.5): the uniform clearing of the even scalar](equation-e5-integrality.md)
- [(E.6): the length of global $H^2$](equation-e6-global-h2-length.md)
- [(E.7): the central valuation before the local terms](equation-e7-central-valuation.md)
- [(E.8): the central calibration of the even scalar](equation-e8-central-calibration.md)
- [(E.9): the lower bound for $v_2L_*$](equation-e9-lower-bound.md)
- [(E.10): Waldspurger's ratio of squared coefficients](equation-e10-waldspurger-ratio.md)
- [(E.11): the actual even form and its rational phase](equation-e11-rational-phase.md), with the form
  and the minimum of Proposition E.4
- [(E.12): the good $T(p^2)$ recurrence](equation-e12-hecke-recurrence.md)
- Proposition E.2, one integral even scalar for the family, has no single declaration; its two
  memberships have their own pages, [(E.4a)](equation-e4a-height-one-valuations.md) and
  [(E.5)](equation-e5-integrality.md), and (E.3) and (E.4) are on this page.
- Proposition E.3, the central calibration of the even scalar, has no single declaration, and each
  of its conclusions is stated: [(E.8)](equation-e8-central-calibration.md), the lower bound
  [(E.9)](equation-e9-lower-bound.md), and the zero criterion $u_h(0)=0\iff L_*(h)=0$ at corank
  zero, the field `zero_iff` of `EvenFamilyOutput` (an abstract form, from (E.4) in coordinates and a
  nonzero reciprocity factor, is proved as `central_zero_iff_of_wedge`).
- Proposition E.4, the actual even form, has no single declaration; its form, (E.11) and its minimum
  are on the page of [(E.11)](equation-e11-rational-phase.md), and its recurrence is
  [(E.12)](equation-e12-hecke-recurrence.md).

The display (K9) has the shape of (3.1); its value at the centre is on the page of
[Proposition 7.2](../section-7/proposition-7-2-even-scalar.md), and the factor itself, as an element of
the group ring, is on the page of [(E.1)](equation-e1-finite-identity.md). The displays (E.3) and (E.4)
are on this page.

## Items with no Lean statement

- **Proposition E.1, with (K1)–(K3).** No declaration states the retained class $Z_F$ (K1), its
  height-one divisibility (K2) or its central reciprocity (K3); `AppEFromKato` asserts only their
  consequences. (K2) is a hypothesis of [(E.4a)](equation-e4a-height-one-valuations.md), and (K3),
  with its fixed factors absorbed, is a field of the input of [(E.8)](equation-e8-central-calibration.md)
  relating recorded integers.
- **The displays of its proof** (K4), (K8) and (K12)–(K16), all inside `AppEFromKato`; Kato's classes
  appear in Lean only as abstract data of the printed interface.
  Two checks are proved: the twisted sum $\beta_\chi=\sum_g\chi(g)\,g\beta$ is a $\chi$-eigenvector
  (`twistedSum_smul`), and the signed identity $L(E^h,1)/(\Omega^\epsilon\sqrt h)=L_*(h)/h$ behind (K14)
  (`K14_normalization`).
- **The displays (E.3) and (E.4) of Proposition E.2** (see Definitions).

## Remaining hypotheses that cover Appendix E

Appendix E enters the Lean proof of Theorem 5.3 only through fields of
[the remaining hypotheses](../remaining-hypotheses.md); its other named inputs (Kato's construction,
`KatoZetaLeaf`, a printed result; the interface data of [(E.1)](equation-e1-finite-identity.md);
Waldspurger's two theorems and Ramsey's model, whose kinds are on the page of
[(E.11)](equation-e11-rational-phase.md)) are not inputs of the reduction. With the kind each
docstring gives:

- `PreLeaves.odd_staged` (GLUE, ELLIOT, PRINT and definitions) is the only field whose docstring cites
  lines of Appendix E: the real-period convention for $L_*(h)$, as part of the normalization of
  $L_*$ (GLUE, Birch–Manin).
- `PreLeaves.even_upper` (ELLIOT) asks for (3.2), which Appendix E proves through Proposition 7.2, and
  for [(3.3a)](../section-7/equation-3-3a-unit-symbol-bound.md), which the manuscript reads from the
  form of Proposition E.4; its docstring cites Section 7 and Appendix G lines.
- `PostLeaves.address` (ELLIOT and GLUE) contains, in `AddressDensityLeaf`, the clause `EvenReading`
  (ELLIOT): (F.1)'s conclusion for the final companion's transported even source, which the
  manuscript reads from (E.11). The field's docstring cites Appendix F and G lines; the clause's own
  docstring cites the lines of Appendix E that derive it with the Waldspurger comparison.

## Sources

- [Appendix E](../../../sources/manuscript.md#appendix-e)
