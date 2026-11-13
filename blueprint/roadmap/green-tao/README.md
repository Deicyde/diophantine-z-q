---
article_id: af_e0cbb3ed73d777ef9d64fd12
---

# Szemerédi's theorem in the primes (Green–Tao)

Route AP replaces the twenty-two-prime pattern by long arithmetic progressions of good slope
primes. They come from two theorems: the good slope primes have positive relative density
(Proposition D), and every set of primes of positive relative upper density contains arithmetic
progressions of every finite length (Green and Tao, Theorem 1.2). This chapter proves the second in
Lean. It is the only part of the formalization that rests on code not written in this project: the
Lean proof of the Green–Tao theorem for the set of all primes by Vasily Ilin, from the repository
Vilin97/Autoformalization (directory `green-tao/`), distributed under the Apache License 2.0 and
vendored in this repository with its license and a notice of the changes made to port it. The
chapter extends that proof to dense sets of primes without changing any vendored file.

Notation: $\lambda_{\alpha,W,b}$ is the W-tricked prime weight on $\mathbb Z/N$ and
$\lambda^A_{\alpha,W,b}$ its restriction to a set $A$; $\Lambda_k(f)$ is the normalized count of
$k$-term progressions in $\mathbb Z/N$ weighted by $f$.

## The statements

- [Szemerédi's theorem in the primes](dense-form.md)
- [The Green–Tao theorem](primes.md)

## From density to windows

The density hypothesis counts all of $[0,N]$ at infinitely many $N$; the W-trick samples a window
$(X/4,X]$ at a scale tied to the cyclic modulus. A dyadic decomposition and Chebyshev's lower bound
put a fixed share of the mass into some window of ratio $2$, and Bertrand's postulate chooses a prime
modulus whose sampled window contains most of it.

- [The window lemma](window-lemma.md)
- [Choosing the prime modulus](modulus-selection.md)

## The weight of a set of primes

The weight of $A$ is the prime weight times the indicator of $A$. It lies below the prime weight, so
majorization and the height bound carry over; positivity now means membership in $A$, and the
residue pigeonhole runs over the elements of $A$ only.

- [The W-tricked weight of a set of primes](set-weight.md)
- [Extraction of a progression in the set](extraction.md)
- [The residue pigeonhole for a set of primes](residue-pigeonhole.md)

## Transference

The relative Szemerédi theorem of the vendored proof holds for every weight below the sieve
majorant; restated for every large prime modulus and every density, it applies to the weight of $A$.

- [Transference for every large prime modulus](prime-modulus-transference.md)

## Assembly

- [Progressions in a set of primes with mass in dyadic windows](window-progressions.md)
- [Szemerédi's theorem in the primes holds](dense-theorem.md)
