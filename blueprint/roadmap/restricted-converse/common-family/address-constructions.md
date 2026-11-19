---
declaration: theorem
origin: cited
---

# The address constructions

For $b\ge1$ an *address* is $x\in\mathbb F_2^b$. A vertex with activation $\lambda\in(\mathbb F_2^b)^*\setminus\{0\}$ is
present at $x$ exactly when $\lambda(x)=1$, and stationary vertices are present at every address. At a fixed
address, a symbol is a function of the independent pair bits between the active terminals; its multilinear
polynomial over $\mathbb F_2$ is the *terminal polynomial*.

Fix coefficient symbols satisfying the coefficient rules, and $b\ge1$.

1. *(One symbol, stationary base.)* If a nonempty stationary terminal list, with its types and any stationary
   external data, has nonzero terminal polynomial and total data in the source's filter, then finitely many new
   primary vertices with nonzero linear activations can be adjoined, choosing only their own incidences, so
   that the symbol is one at every $x\ne0$. The original vertices and data are unchanged, and no new vertex is
   present at $0$.
2. *(Two symbols, one family.)* Let one or two symbols read separately surjective projections of one common
   alphabet, and fix terminals with nonzero linear activations, including one of every nonzero activation.
   If at every $x\ne0$ the active configuration is nonempty, satisfies every filter, and each symbol separately
   has a nonzero terminal polynomial, then finitely many new primary vertices can be adjoined so that all the
   symbols are one at every $x\ne0$, preserving all original data and the zero address.

A nonzero iterated difference, hence a contraction certificate, suffices for a nonzero terminal polynomial. For an
odd limit symbol these are statements about finite typed graphs; the theta stage is chosen afterwards, and only
then the primes.

**Proof sketch.** Network operators are built from grounded Laplacian minors: for a network with matrix $Q$ the
operator is $\det(Q)+\sum c_a^t\operatorname{adj}(Q)c_bd_{ab}+(\text{terms of degree}\ge2)$, which expresses the
constant and pair-contraction operators, singular matrices included. A singular network $T=I+P$, with
$\operatorname{adj}(Q)=rr^t$, isolates a prescribed derivative at one nonzero address and is constant one elsewhere;
a varying network $T=I+L$ supplies the corresponding difference when two symbols share a variable. For two
symbols, take the top monomial $M_x$ of $H_{1,x}H_{2,x}$, with exponents at most two, in the ordinary polynomial ring
before Boolean reduction: a variable of exponent two uses one singular program in each factor and exponent one a
varying program. In
$$\sum_\varepsilon\prod_{y\ne0}\prod_{s=1}^2A_s(\Gamma_y(\varepsilon))\tag{G.1a}$$
the total degree kills every other contraction, so the sum equals $\prod_x[M_x]\,(H_{1,x}H_{2,x})=1$, and some choice
$\varepsilon$ works at every $x\ne0$ at once. The one-symbol case is the specialization with stationary terminals.

## Depends on

- [Compatible typed graphs and coefficient symbols](coefficient-symbols.md)
- [Arithmetic realization of the coefficient rules](coefficient-rules.md)

## Proof depends on

- [Finite realization, unit seeds and contraction certificates](seeds.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:sec7-address`, `ex:sec7-one-symbol-address` and
  `ex:sec7-two-symbol-address` (L2209–2288), `ex:app-simultaneous-address` (L10554–10790)

## Manuscript check

Mapped by AI review and read for structure. The $\mathbb F_2$ linear algebra of the singular and varying
networks was checked by script for $b\le6$. The degree count (G.1a) was read but not re-derived; it is not yet
checked.
