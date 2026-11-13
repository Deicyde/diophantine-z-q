---
article_id: af_76f444b0457a7c7577a0780e
declaration: def
origin: background
statement: formalized
lean: ZInQ.GreenTaoDense, ZInQ.ContainsArbitraryAPs, ZInQ.PrimesRelUpperDensityPos
---

# Szemerédi's theorem in the primes

A set $A$ of natural numbers *contains arithmetic progressions of every finite length* if for every
$k$ there are natural numbers $a$ and $b\ge1$ with $a+bj\in A$ for every $j<k$. A set $A$ has
*positive relative upper density in the primes* if there is a real $c>0$ such that
$$c\,\pi(N)\le\#\bigl(A\cap[0,N]\bigr)$$
for infinitely many $N$, where $\pi$ is the prime counting function; for a set of primes this says
$\limsup_{N\to\infty}\#(A\cap[1,N])/\pi(N)>0$.

Szemerédi's theorem in the primes, in its dense form, is the assertion that every set of primes of
positive relative upper density contains arithmetic progressions of every finite length.

This is Theorem 1.2 of Green and Tao, with "infinitely many progressions" weakened to "one".
Green and Tao prove it in outline; Tao and Ziegler give a complete proof. Route AP needs it for the
good slope primes above $\max S_b$. It was first a hypothesis of the route AP variants of the main
theorem; it is proved in this chapter
([Szemerédi's theorem in the primes holds](dense-theorem.md)).

## Depends on

None.

## Sources

- [Green and Tao](../../sources/green-tao-locators.md#green-and-tao)
- [Tao and Ziegler](../../sources/green-tao-locators.md#tao-and-ziegler)
