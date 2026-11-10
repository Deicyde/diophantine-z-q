# Locators for the Green–Tao chapter

The Green–Tao chapter is not in the manuscript. It supplies, in Lean, the input of route AP:
Szemerédi's theorem in the primes, for sets of primes of positive relative upper density. The
plan is a project-authored research note, `docs/research/gt-dense.md`; it is a specification
written for this project, not a published source. The proof for the set of all primes is a
vendored third-party Lean development, and the published theorems are cited at the end.

## The vendored proof

`ThirdParty/GreenTao/NOTICE.md`: the Lean proof of the Green–Tao theorem for the set of all primes,
from the repository Vilin97/Autoformalization (directory `green-tao/`, commit
`0dc67d87416c19690dd641a178ada32cca95c651`), produced under the direction of Vasily Ilin as a
submission to the `green_tao` target of the lean-eval benchmark, distributed under the Apache
License 2.0 (`ThirdParty/GreenTao/LICENSE`). It was ported to the Lean and Mathlib versions of this
repository with proof edits only; no statement was changed. The trusted statement is
`ThirdParty/GreenTao/ChallengeDeps.lean`.

## Where the primes enter

`docs/research/gt-dense.md` §1: the assembly chain of the vendored proof, the W-tricked prime
weight, density selection, majorization, diagonal negligibility, extraction and small lengths;
§2: the relative counting step holds for every weight below the majorant.

## The proof for a dense set

`docs/research/gt-dense.md` §3: the seven steps (window lemma, density, transference for every
large prime modulus, Bertrand modulus selection, residue pigeonhole for the set, count and
extraction, small lengths) and the table §3.1 of the places where the original proof uses a
property of the set of all primes.

## The Lean statements

`docs/research/gt-dense.md` §4–§5: the weight of a set of primes, the transference for every
large prime modulus and every sub-weight, density selection for the set, the window lemma and the
modulus selection, extraction and the final assembly. The Lean files are
`ZInQKernel/External/GreenTaoDense/` (`Window.lean`, `SetWeight.lean`,
`PrimeModulusTransference.lean`, `Assembly.lean`); the files adapted from the vendored proof carry
Apache License notices naming their source files. The window lemma in Lean uses only Chebyshev's
lower bound for the prime counting function, with the tail of the dyadic decomposition bounded
trivially (module docstring of `Window.lean`).

## Green and Tao

B. Green and T. Tao, *The primes contain arbitrarily long arithmetic progressions*, Ann. of Math.
167 (2008), 481–547: Theorem 1.1 (the primes contain arbitrarily long arithmetic progressions) and
Theorem 1.2 (Szemerédi's theorem in the primes: every set of primes of positive relative upper
density contains arithmetic progressions of every finite length). Theorem 1.2 is proved there in
outline (section 11 of arXiv math/0404188v6).

## Tao and Ziegler

T. Tao and T. Ziegler, *The primes contain arbitrarily long polynomial progressions*, Acta Math.
201 (2008), 213–305: a complete proof of Szemerédi's theorem in the primes, as a special case.
