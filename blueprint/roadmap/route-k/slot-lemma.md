---
article_id: af_4c043865e6c0472162a6da42
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.exists_prime_slot, ZInQ.RouteK.exists_prime_slot_bits
---

# The slot lemma

Let $S$ be a finite set of odd primes with signs $\varepsilon_p\in\{\pm1\}$ ($p\in S$), let $a$
be an odd integer and $A$ a finite set of natural numbers. Then there is a prime $q\notin A$ with
$q\equiv a\pmod8$ and $(q/p)=\varepsilon_p$ for every $p\in S$.

Equivalently, in residue bits: for prescribed bits $b_p\in\mathbb F_2$ ($p\in S$) there is a prime
$q\notin A\cup S$ with $q\equiv a\pmod8$ and $[q/p]=b_p$ for every $p\in S$.

**Proof sketch.** Every odd prime $p$ has $(p-1)/2\ge1$ nonzero squares and as many non-squares
modulo $p$, so some residue $r_p$ prime to $p$ has $(r_p/p)=\varepsilon_p$. By the Chinese
remainder theorem the conditions $q\equiv a\pmod 8$ and $q\equiv r_p\pmod p$ ($p\in S$) define
one invertible class modulo $8\prod_{p\in S}p$, and by Dirichlet's theorem on primes in
arithmetic progressions it contains a prime larger than every element of $A$ (and of $S$).

## Depends on

- [Residue bits](residue-bits.md)

## Sources

- [Slots](../../sources/route-k-locators.md#slots)
