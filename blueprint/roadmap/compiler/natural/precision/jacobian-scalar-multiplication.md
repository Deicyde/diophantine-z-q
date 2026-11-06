---
article_id: af_07918e9967c49a605a97d420
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Precision.rep_jmul, ZInQ.Compiler.Precision.jmul_eq_some, ZInQ.Compiler.Precision.admissible_iff_jmul
---

# Scalar multiplication by halving

A *Jacobian representative* of a point of $E(K_0)$ is a triple $(X,Y,Z)\in\mathbb Z[s]^3$
representing $O$ when $Z=0$ and the affine point $(X/Z^2,Y/Z^3)$ when $Z\ne0$ (which then
lies on $E$ whenever $\mathcal E(X,Y,Z)=0$). Let $\oplus$ be the branching addition: if one
argument has $Z=0$ return the other; otherwise compute $H,\Lambda$; if $H\ne0$ return
$\mathrm{add}$; if $H=0$ and $\Lambda=0$ return $\mathrm{dbl}$ (or $O$ if $Y=0$); if $H=0$ and
$\Lambda\ne0$ return $O$. Let $\mathrm{dbl}^\ast$ be doubling with $O\mapsto O$ and zero ordinate
$\mapsto O$.

For $k\in\mathbb N$ define $\mathrm{mul}(k)$ by the loop with state $(\Pi,\Theta,e)$ starting at
$(O,P^{\rm J}_0,k)$, where $P^{\rm J}_0=(3282-2320s,-247440+174966s,4)$ and $O=(1,1,0)$: while
$e>0$, if $e$ is odd replace $\Pi$ by $\Pi\oplus\Theta$; replace $\Theta$ by $\mathrm{dbl}^\ast(\Theta)$
and $e$ by $\lfloor e/2\rfloor$; return $\Pi$. For a negative integer $k$ let $\mathrm{mul}(k)$ be
the negation $(X,-Y,Z)$ of $\mathrm{mul}(-k)$.

Then for every $k\in\mathbb Z$ the loop terminates and $\mathrm{mul}(k)$ is a Jacobian
representative of $[k]P_0$ satisfying $\mathcal E=0$; in particular $[k]P_0=O$ if and only if
the third coordinate is $0$, and otherwise its ordinate is zero if and only if the second
coordinate is $0$.

**Proof sketch.** Termination: $e$ halves. Invariant: $\Pi$ and $\Theta$ represent points
$\pi,\theta$ on $E$ with $\pi+[e]\theta=[k]P_0$; it holds initially because $O=(1,1,0)$
represents $O$ and $P^{\rm J}_0$ represents $P_0$ (the fixed Jacobian point) and is preserved because $\oplus$ and $\mathrm{dbl}^\ast$ represent the group law
(Jacobian formulas, items 1-8): if $e$ is odd, $\pi+[e]\theta=(\pi+\theta)+[e-1]\theta$, and
$[2\lfloor e/2\rfloor]\theta=[\lfloor e/2\rfloor](2\theta)$. At $e=0$, $\pi=[k]P_0$. Negation
represents $-P$. The last claim: for $Z\ne0$, $y=Y/Z^3$.

## Depends on

- [Jacobian formulas on the weighted model](jacobian-formulas.md)
- [The point $P_0$](../../../model/field/generator-point.md)

## Proof depends on

- [The fixed Jacobian point](jacobian-generator.md)

## Sources

- [Section 10 reference program and IR](../../../../sources/compiler-natural-locators.md#section-10-reference-program-and-ir)
- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
