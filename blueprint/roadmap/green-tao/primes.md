---
article_id: af_dfb09b8d14338f0fea503569
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.greenTao_primes, Submission.green_tao
---

# The Green–Tao theorem

The set of primes contains arithmetic progressions of every finite length: for every $k$ there are
natural numbers $a$ and $b\ge1$ such that $a+bj$ is prime for every $j<k$.

This is Theorem 1.1 of Green and Tao. Its Lean proof is not written in this project: it is
Vasily Ilin's proof from the repository Vilin97/Autoformalization (directory `green-tao/`, commit
`0dc67d87416c19690dd641a178ada32cca95c651`), produced under Ilin's direction as a submission to the
`green_tao` target of the lean-eval benchmark and distributed under the Apache License 2.0. It is
vendored in this repository with its license and a notice, and ported to the project's Lean and
Mathlib versions with proof edits only; its statement is unchanged, and it is the statement here,
since the two definitions of "contains arithmetic progressions of every finite length" agree word
for word.

**Proof sketch.** The vendored proof follows Green and Tao. After the W-trick (restricting to a
reduced residue class $b$ modulo $W=\prod_{p\le w}p$ and weighting the primes $Wn+b$ by
$\log(Wn+b)$), the weighted primes in a cyclic group $\mathbb Z/N$ of prime order are bounded by a
Selberg-sieve majorant $\nu$ that satisfies the linear forms condition. The relative Szemerédi
theorem (transference: a weight $0\le f\le\nu$ of positive mean has a dense model) and the dense
Szemerédi theorem, from the hypergraph removal lemma, give a positive count of $k$-term
progressions weighted by $f$; the diagonal progressions are negligible, so some progression with
nonzero difference has positive weight at every term, and a short-interval lift turns it into a
progression of primes. Lengths $k\le2$ come from the progression $2,3$.

## Depends on

- [Szemerédi's theorem in the primes](dense-form.md)

## Sources

- [The vendored proof](../../sources/green-tao-locators.md#the-vendored-proof)
- [Green and Tao](../../sources/green-tao-locators.md#green-and-tao)
