---
article_id: af_94ef7a6085b4f93bd757c8e6
declaration: def
origin: cited
statement: formalized
lean: ZInQ.AlphaPower.PowEqns
---

# The power formula

For natural numbers $P,Q,R$, the *power formula* $\mathrm{Pow}(P,Q,R)$ is the disjunction of
three branches:

1. $Q=0$, $R=0$ and $P=1$;
2. $Q=0$, $0<R$ and $P=0$;
3. $0<Q$ and there are natural numbers $b,m,a_0,a_1,a_2$ with (C.3)
   $$\mathrm{Alpha}(a_0,Q+4,R+1),\quad b=a_0+Q^2+2,\quad m+Q^2+1=bQ,\quad P<m,$$
   $$\mathrm{Alpha}(a_1,b,R),\quad \mathrm{Alpha}(a_2,b,R+1),\quad P+ba_1\equiv Qa_1+a_2\pmod m .$$

The compiler's power macro introduces $b,m,a_0,a_1,a_2$ in this order (before the
witnesses of the inner macros), writes the strict inequalities $0<R$, $0<Q$, $P<m$ and the
congruence with the equational gadgets, and writes the three alpha formulas as alpha
macros; the three branches are joined by a disjunction, each branch being a conjunction.
The third branch is `Exponential_Relation.exp_repr` of the AFP development.

This is a definition.

## Depends on

- [The alpha formula](alpha-equations.md)

## Sources

- [Section 10.2 power formula](../../../../sources/compiler-natural-locators.md#section-102-power-formula)
- [Compiler source](../../../../sources/compiler-natural-locators.md#compiler-source)
- [AFP DPRM development](../../../../sources/compiler-natural-locators.md#afp-dprm-development)
