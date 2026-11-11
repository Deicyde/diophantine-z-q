---
article_id: af_e32388e618d70d75466eb859
---

# Proposition 0: the explicit system is the 2-Selmer group

The certified rank hypothesis CR₃ of the main theorem is stated on the explicit linear system
$\Sigma(\mathcal C_d)$ of the [Route K chapter](../route-k/README.md), built from classes modulo
$8$ and Legendre symbols. Proposition 0 says that for squarefree $d\equiv5\pmod8$ the solutions of
this system are, in coordinates, the 2-Selmer group of the congruent number curve
$C_d:y^2=x^3-d^2x$, defined by the local solubility of its 2-coverings. This chapter proves it, and
so replaces CR₃ by the narrower hypothesis CR₃^Sel, stated on the Selmer group itself: when
$\mathrm{Sel}_2(C_d)$ has dimension $3$ and contains a class with $|a|\equiv7\pmod8$, every Selmer
class comes from a rational point.

Throughout, $C_d$ is $y^2=x(x-d)(x+d)$, and $u\equiv v$ means that $u/v$ is a nonzero square.

## Coverings

The 2-coverings $D_{a,b}$ of $C_d$ are written in an x-form, which depends only on the square
classes of $a$ and $b$; over any field of characteristic not $2$ a covering is soluble exactly when
$(a,b)$ is a Kummer image of a point.

- [The 2-coverings of a congruent number curve](coverings.md)
- [The x-form of a covering](covering-x-form.md)
- [Square classes and torsion witnesses of a covering](covering-classes.md)
- [Coverings and the Kummer map](kummer-map.md)

## Local solubility

At each place the soluble classes are computed: by sign at the real place, by Hensel's lemma and
square classes at the finite places. At odd primes not dividing $d$ every unit pair is soluble,
through a residue witness over $\mathbb F_p$ found with Jacobsthal's bound on cubic character sums
(and a kernel check for $p<29$); at odd primes dividing $d$ only the four torsion classes are
soluble; at $2$, for odd $d$, the torsion classes and their products with $(1,5)$.

- [Squares in the p-adic numbers](padic-squares.md)
- [Local solubility at the real place](real-place.md)
- [A residue witness for the coverings over a finite field](character-sums.md)
- [Local solubility at odd primes not dividing d](good-primes.md)
- [Local solubility at odd primes dividing d](bad-odd-primes.md)
- [Local solubility at the place 2](place-two.md)

## The Selmer group and Proposition 0

The 2-Selmer group is the set of pairs of squarefree integers whose covering is soluble at every
place. Reading the local classes off in residue bits turns the local conditions into the rows of
$\Sigma(\mathcal C_d)$.

- [The 2-Selmer group of a congruent number curve](selmer-group.md)
- [The local conditions are the rows of the Selmer system](local-rows.md)
- [Proposition 0](proposition-0.md)

## The certified rank hypothesis in Selmer form

CR₃^Sel also follows from its positive-rank form CR₃^Rk, which under the same premises asks only
that $C_d(\mathbb Q)$ have a point of infinite order, by RK9 and Mordell–Weil for $C_d$, both proved
([the positive-rank chapter](../rank/README.md)).

- [The certified rank hypothesis in Selmer form](certified-rank-sel.md)
- [The certified rank hypothesis from its Selmer form](certified-rank-of-sel.md)
