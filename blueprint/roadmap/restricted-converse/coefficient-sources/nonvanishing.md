---
declaration: theorem
origin: cited
---

# Nonvanishing in a prescribed unit filter

A signed unit filter prescribes a real sign and unit squareclasses at a finite set $S$ of primes
containing $2$, $3$ and the bad primes; let $B$ be any further finite set of forbidden primes. If the root
number of the filter is even, it contains a squarefree parameter prime to $B$ with at most five prime
factors and nonzero central value. If it is odd, it contains a parameter at which $L$ has a simple zero,
with no bound on the number of prime factors. The bound five does not depend on $S$ or $B$.

In the form of Appendix G: for a fixed modular elliptic curve $A/\mathbb Q$ and every nonempty signed
unit filter at $S$ of even root number, there is a signed odd squarefree $u$ prime to $S\cup B$ with
$L(A^u,1)\ne0$ and $\omega(u)\le5$. Only the intermediate parameter needs to be fundamental; the final field
discriminant may be $4u$. No bound on the sizes of the primes is asserted.

**Proof sketch.** By Dirichlet's theorem choose a signed prime $q_0$ in the prescribed unit classes,
outside $S\cup B$. Apply Hoffstein–Luo (p. 436) in the even case, or the simple-zero clause of
Bump–Friedberg–Hoffstein in the odd case, to the twist $E^{(q_0)}$, asking that their positive
discriminant $d$ split at $S\cup B\cup\{|q_0|\}$ and at the conductor primes. Then $q_0d$ has the prescribed
classes, and Hoffstein–Luo gives at most four prime factors of $d$, so at most five in all. The root numbers
are checked locally: equal squareclasses at $S$ give isomorphic local curves, and at a good odd prime newly
ramified in the parameter the local root factor is $(-1/p)$ (Desjardins, Proposition 3.3), whose product
outside $S$ is fixed by the sign and the dyadic unit class. In the even case of Appendix G, $d>0$ is forced
by the functional equation and $d\equiv1\pmod 8$.

## Depends on

None.

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:sec7-nonvanishing` (L1968–2004) and
  `ex:app-five-prime` (L9995–10054)

## Manuscript check

Mapped by AI review, as a reduction to the two cited theorems. The statements used, Hoffstein–Luo's "at
most four prime factors with an arbitrary finite splitting set" and the simple-zero clause of
Bump–Friedberg–Hoffstein, and Desjardins' Proposition 3.3, are not yet checked against the prints.
