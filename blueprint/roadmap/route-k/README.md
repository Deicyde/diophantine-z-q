---
article_id: af_227585a2d1d47bd1ca422fc3
---

# Pole completeness from certified rank (Route K)

The manuscript's pole polynomial puts two points on curves $y^2=x(x-\ell)(x+3\ell)$, and the
manuscript derives pole completeness from its restricted converse theorem, whose proof uses
Kato's Euler system, Waldspurger's formula, Bump–Friedberg–Hoffstein and Nekovář's Selmer
complexes. Route K changes the polynomial to the congruent number curves
$C_\ell:y^2=x(x-\ell)(x+\ell)$; the elementary direction, Lemma 5.1, is unchanged
([the one-sided pole obstruction](../multiplication/pole-obstruction.md)). This chapter proves
pole completeness for the new polynomial from one narrow hypothesis on congruent number curves,
the [certified rank hypothesis](../main/certified-rank.md) CR₃, by an explicit descent: for every
admissible input $B$ it produces two curves $C_n$ and $C_{n\theta}$ whose 2-Selmer groups, written
as an $\mathbb F_2$-linear system in Legendre symbols, have dimension $3$ and contain the class
$\beta$. CR₃ turns these certificates into rational points, and two such points give a zero of
the pole polynomial.

Throughout, $C_d$ is the curve $y^2=x^3-d^2x$; it depends only on $d^2$.

## Configurations and the Selmer system

An odd squarefree $d>0$ is recorded by its primes, their classes modulo $8$ and their
Legendre symbols; Proposition 0 writes the 2-Selmer group of $C_d$ as the solutions of a linear
system in these data. The system makes sense for any configuration, realized by a number or
not.

- [Configurations](configuration.md)
- [The Selmer system of a configuration](selmer-system.md)

Two operations shrink a configuration and carry its solutions bijectively onto those of the
smaller one, keeping $a_0,a_1,b_0,b_1$: removing a glue prime with a single partner, and gluing
a set of primes into one virtual prime through glue primes.
At the end of the reduction stands a configuration of two primes, whose system is computed
directly.

- [The partner lemma](partner-lemma.md)
- [The gluing lemma](gluing-lemma.md)
- [The base configuration](base-configuration.md)

## Residue bits and actual numbers

- [Residue bits](residue-bits.md)
- [Quadratic reciprocity in residue bits](reciprocity-bits.md)
- [The configuration of an odd number and Selmer certificates](prime-configuration.md)

## The inputs $\beta$ and $\theta$

An admissible input $B$ and a signed divisor $m$ of $2730$ determine the squarefree parts
$\beta=\mathrm{sqf}(mB)$ and $\theta=\mathrm{sqf}(m(m-B))$. The multiplier is chosen so that
$|\beta|\equiv7\pmod8$, and $\theta$ then has four local properties.

- [Admissible inputs, the squarefree part, $\beta$ and $\theta$](squarefree-part.md)
- [The multiplier lemma](multiplier-lemma.md)
- [The properties (θ1)–(θ4)](theta-properties.md)

## The slots

The auxiliary primes are chosen by Dirichlet's theorem with prescribed residue bits: one prime
$q_0\equiv3\pmod8$, glue primes $r_p\equiv1\pmod8$ that glue the primes of $\beta$ into one
virtual prime of class $7$, and glue primes $r_\ell\equiv1\pmod8$ that hang the primes of $\theta$
on $q_0$.

- [The slot lemma](slot-lemma.md)
- [The slot conditions](slot-conditions.md)
- [The slots exist](slots.md)

## The descent lemma

With $n=|\beta|q_0\prod r_p\prod r_\ell$, the partner and gluing lemmas reduce the configurations of
$|n|$ and $|n\theta|$ to the base configuration, and the class $\beta$ survives every step.

- [The realization: both curves reduce to the base configuration](realization.md)
- [The descent lemma](descent-lemma.md)

## From points to pole completeness

Two points with abscissas in $\beta\mathbb Q^{*2}$ on $C_N$ and $C_{N\theta}$ rescale to the
witnesses of the pole polynomial. With CR₃ applied to the two certified curves this proves pole
completeness, which the main theorem therefore no longer assumes. The proof applies CR₃ to these
two curves only; the [two-curves section](../rank/two-curves/README.md) proves pole completeness
from positive rank on curves of the same kind: the two curves of some slot choice, for every
triple $\beta,\theta,p_0$ satisfying the hypotheses of the realization (CR₃^DL,Rk), or, for each
admissible input, for some multiplier, prime $p_0\mid\beta$ and slot choice (CR₃^DL,Adm,Rk).

- [Points on two congruent number curves give pole solubility](points-pole-solubility.md)
- [Pole completeness from the certified rank hypothesis](pole-completeness-from-cr3.md)
