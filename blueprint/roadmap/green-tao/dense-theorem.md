---
article_id: af_de9b8d9f8aeac3e47f171e4d
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.greenTaoDense
---

# Szemerédi's theorem in the primes holds

Every set of primes of positive relative upper density contains arithmetic progressions of every
finite length.

This is Theorem 1.2 of Green and Tao (in the weakened form of
[Szemerédi's theorem in the primes](dense-form.md)), proved here by extending the vendored Lean
proof of [the Green–Tao theorem](primes.md) from the set of all primes to dense subsets. No vendored
file is changed: the steps that use a property of the set of all primes are redone for the subset in
new files, those adapted from vendored proofs under the vendored proof's Apache License.

**Proof sketch.** Let $A$ be a set of primes of positive relative upper density and $k$ a length.
The window lemma gives $c_1>0$ with $\#(A\cap(\lfloor Z/2\rfloor,Z])\ge c_1Z/\log Z$ for infinitely
many $Z$. Transference holds for every large prime modulus and every weight below the W-tricked
prime weight, so the theorem on progressions in a set with mass in dyadic windows applies and gives
a $k$-term progression in $A$ with positive difference.

The proof for all primes uses three properties that a dense set lacks: Chebyshev's lower bound in
the fixed window $(X/4,X]$ at every large scale, a modulus chosen freely after the density, and the
progression $2,3$ for the small lengths. They are replaced by the window lemma, the Bertrand modulus
selection with transference at every large prime modulus, and truncation of a progression of
length $3$.

## Depends on

- [Szemerédi's theorem in the primes](dense-form.md)

## Proof depends on

- [The window lemma](window-lemma.md)
- [Transference for every large prime modulus](prime-modulus-transference.md)
- [Progressions in a set of primes with mass in dyadic windows](window-progressions.md)

## Informally uses

- [The Green–Tao theorem](primes.md)

## Sources

- [The proof for a dense set](../../sources/green-tao-locators.md#the-proof-for-a-dense-set)
- [Green and Tao](../../sources/green-tao-locators.md#green-and-tao)
- [Tao and Ziegler](../../sources/green-tao-locators.md#tao-and-ziegler)
