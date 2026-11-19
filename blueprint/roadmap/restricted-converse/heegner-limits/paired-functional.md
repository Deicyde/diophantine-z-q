---
declaration: theorem
origin: cited
---

# The paired functional and the class-functional coordinate

Use the retained inner-limit diagrams with the local conditions of this section, and let $z$ be the actual
retained class. Transporting $z$ by conjugation, lifting it through the orthogonal comparison $j$ at the
generic point and pairing by the retained duality defines one closed degree-two functional
$\lambda_z=\operatorname{PD}(-,j^{-1}c(z))$. It has an integral representative over $\mathscr O[G]$ after
multiplication by $2^a$, for a fixed old-support exponent $a$ independent of the active list and of $G$. For
a scalar constituent with its primitive local conditions, the functional has an integral representative at
every height-one prime $\mathfrak p\ne(2)$ of $\Lambda$, including $(t)$ and $(t+2)$, with the same generic
value. The universal relaxed functional is asserted integral only after the fixed power of two over
$\mathscr O[G]$.

For a constituent whose generic cohomology has dimensions $(1,1)$ in degrees one and two and vanishes
otherwise, the *class-functional coordinate* $u$ is the coordinate of $[z]\otimes[\lambda_z]$ in the determinant
line $\det^{-1}C\simeq H^1(C)\otimes H^2(C)^*$, in the retained integral basis; for a generically acyclic
constituent $u=0$. The subscripts "prim" and "rel" record the primitive and relaxed local conditions.

**Proof sketch.** Over $\mathscr O=\widehat{\mathbb Z_2[[t]]_{(2)}}$ the residual active Frobenius is
$(1+t)^eI$ with $e$ odd, so $A=\Phi-1$ and $D$ in (4.4) are units over $\mathscr O[G]$, and the full local
complex at an active place has the explicit Frobenius contraction $h^1=A^{-1}v$, $h^2=(0,D^{-1}u)$. At the
moving prime $C=t\cdot I$ and $t$ is a unit of $\mathscr O$; at a height-one $\mathfrak p\ne(2)$ the active
inertia gives $C=-2$, a unit. At $(t)$ the inertia contraction fails, and the Frobenius contraction works
instead because $\det(1-\Phi_0)=2-\lim\chi_h(r_i)a_{r_i}$ is nonzero, by the bound $v_2(2\pm a_r)\le c_E$ of the
moving character, which survives the ultrafilter limit; at $(t+2)$, $t\equiv-2$ is a unit. Every allowed $K$
splits at $2N$, so its completions there are $\mathbb Q_p$ and the old-place diagrams come from one fixed
finite list. The group-ring pairing is a permutation matrix, so duality has no group-order denominator. Hence
the cone of $j$ is integrally contractible, $j^{-1}$ is integral, and in fact $a=0$ is allowed, independent
of $G$, the active graph and $K$.

## Depends on

- [Finite free models and the inner limit](inner-limit.md)
- [Local conditions, the derived Kummer condition and duality](local-conditions.md)

## Proof depends on

- [One moving character for the complete active list](moving-character.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:arith-paired-functional` (L3704–3875) and
  `ex:arith-coordinate` (L3877–3892)

## Manuscript check

Checked line by line by AI review, with 28 checks by script, each with a negative control: the Frobenius and
inertia contractions, $DC=CA$, the active units over $\mathscr O[G]$, the moving prime at a finite stage, the
central determinants at $(t)$, the units at $(t)$ and $(t+2)$, the homotopy inverse from a cone contraction,
the group-ring pairing and the old-place bookkeeping. The statement says that $a$ is independent of the
active list and of $G$ but does not mention $K$; uniformity in $K$ is what (5.5) uses, and the proof gives it
(L3808–3818, L3864–3874). The letter $a$ also denotes an odd exponent at L3729, and the remark that $a=0$
because "$z$ already contains $L$" (L3864–3866) gives a different reason from the one that holds: every map
in $\lambda_z$ is integral, whatever $L$ is. The conclusion is unchanged. The integral old-place comparison
taken from the derived Kummer lemma, and the hypotheses of Nekovář 6.2.5–6.2.8 and 6.3.4, are not yet checked.
