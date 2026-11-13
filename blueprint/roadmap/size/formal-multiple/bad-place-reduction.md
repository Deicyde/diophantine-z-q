---
article_id: af_15ca60f1a4296040dd1f25ef
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.genP0_mem_E0_d, ZInQ.Size.redK_genP0_d, ZInQ.Size.resK_genA_d, ZInQ.Size.E0_eq_top_of_ne_d
---

# Reduction of $P_0$ at the bad place

Let $E:y^2=x^3-d^2x$ with $d=75-53s$, $A=-d^2=-11243+7950s$, and
$P_0=\bigl(\frac{1641-1160s}{8},\frac{-123720+87483s}{32}\bigr)$.

1. At the prime $(d)$, with residue map $\rho:a+bs\mapsto a+3b\bmod7$ onto $\mathbb F_7$:
   $\rho(A)=0$, so the reduced curve is $y^2=x^3$; the coordinates of $P_0$ lie in
   $\mathbb Z[s]_{(d)}$ (their denominators are powers of $2$) and reduce to $(2,6)$; and
   $(2,6)$ is a nonsingular point of $y^2=x^3$ over $\mathbb F_7$. Hence $P_0\in E_0((d))$.
2. For every other prime $\mathfrak p$ of $\mathbb Z[s]$ with $2\notin\mathfrak p$, $A\notin\mathfrak p$,
   so $E$ has good reduction at $\mathfrak p$ and $E_0(\mathfrak p)=E(K_0)$.

**Proof sketch.** (1) $\rho$ is the residue map of $(d)$ (model chapter). The congruences
modulo seven (a separate finite computation) give $\rho(8x(P_0))=\rho(8)\cdot2$ and
$\rho(32y(P_0))=\rho(32)\cdot6$ with $\rho(8),\rho(32)\ne0$, so $8,32\notin(d)$, the coordinates
lie in $\mathbb Z[s]_{(d)}$, and $\rho(x(P_0))=2$, $\rho(y(P_0))=6$; also $\rho(A)=0$ and $6^2=2^3$ in $\mathbb F_7$.
A point of $y^2=x^3$ is singular exactly when $2y=0$ and $3x^2=0$; here $2\cdot6=12\not\equiv0$.
(2) $d$ is a prime element and $A=-d^2$, so $A\in\mathfrak p$ only for $\mathfrak p=(d)$; then
apply the good-reduction case of reduction on the nonsingular part.

The manuscript records the reduction to $(2,6)$, its nonsingularity, and good reduction at
the other place $s\equiv4\pmod7$ above $7$.

## Depends on

- [The point $P_0$](../../model/field/generator-point.md)
- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../../model/field/special-primes.md)
- [Reduction on the nonsingular part](reduction-homomorphism.md)

## Proof depends on

- [Congruences for $P_0$ modulo seven](bad-place-congruences.md)

## Sources

- [Proof of Proposition 12.1, formal multiple](../../../sources/size-locators.md#proof-of-proposition-121-formal-multiple)
