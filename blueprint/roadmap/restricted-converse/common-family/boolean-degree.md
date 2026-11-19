---
declaration: theorem
origin: bridged
---

# Bit degrees of sign-value functions and cube parity

Let $G\simeq\mathbb F_2^b$ and identify its sign characters with the addresses $x\in\mathbb F_2^b$. For any
element of $\mathscr O[G]$, the sign-value function of each of its coefficients has the form
$$A(x)=a_\varnothing+\sum_{I\ne\varnothing}2^{|I|}a_I\prod_{i\in I}x_i\qquad(x\in\mathbb F_2^b).$$
Its bit of index $0$ is constant, and its bit of index $j\ge1$ is a Boolean function of degree at most $2^{j-1}$.
Consequently $q$ coefficient congruences modulo $2^M$ define Boolean conditions whose degrees sum to at most
$q(2^{M-1}-1)$. If that sum is less than $b$, the set of addresses satisfying all of them has even
cardinality; since it contains $0$, it contains a nonzero address.

**Proof sketch.** The bit of index $j$ of $A(x)$ is the coefficient of $Y^{2^j}$ in $(1+Y)^{A(x)}$ modulo two.
A monomial $x_I$ enters $A(x)$ with the factor $2^{|I|}$, so its first possible contribution has degree at least
$2^{|I|}$ in $Y$, and $|I|\le2^{|I|-1}$. For the parity statement multiply the complementary indicators of the
conditions: the product has degree less than $b$, so its sum over the cube vanishes, every monomial missing a
variable. Its support is the common solution set, which therefore has even size.

## Depends on

None.

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): inside the proof of
  `ex:limits-coefficient-transfer` (L5666–5684); used in the proof of `ex:sec7-even-upper` (L2324–2331)

## Manuscript check

Checked by AI review and by script: the $(1+Y)^{A}$ argument, by brute force for $b\le6$ on 300 random
elements, and the parity of the support of a Boolean function of degree less than $b$, by brute force. This
lemma is self-contained, which is why the even upper estimate of Section 7 can use it before the Heegner
argument.
