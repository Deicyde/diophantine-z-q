# Theorem A of Breuil–Conrad–Diamond–Taylor, as printed

## Status

`ZInQ.Manuscript.PoleS12.BCDTThmA`, formerly the main row's leaf hB (`ZInQ.OneProof.frozenTarget`
no longer takes hB), follows from the printed statement:

```lean
theorem bcdtThmA_of_printed (hB : BCDTThmAPrinted) : ZInQ.Manuscript.PoleS12.BCDTThmA
```

`BCDTThmAPrinted` is the only input. It is Theorem A of Breuil–Conrad–Diamond–Taylor read with
condition (2) of the Introduction, over Mathlib's cusp forms on `Γ₁(N)` and the vendored Hecke
operators, with one deliberate weakening: the level is an unspecified positive integer rather
than the conductor `N(E)` (the library has no conductor of an elliptic curve). The passage
`Γ₁(N) → Γ₀(N)` (trivial nebentypus) that made `BCDTThmA` a GLUE row is proved. Every
declaration depends only on `propext`, `Classical.choice` and `Quot.sound`.

## The print

C. Breuil, B. Conrad, F. Diamond and R. Taylor, *On the modularity of elliptic curves over `ℚ`:
wild 3-adic exercises*, J. Amer. Math. Soc. 14 (2001), 843–939. The manuscript cites the author
manuscript (bibitem `bcdt`), <https://virtualmath1.stanford.edu/~conrad/papers/tswfinal.pdf>;
the copy read has 79 pages, 685,965 bytes, SHA-256
`13043cf6e9043a69dc7988882658cd92595efc88dfd4fd2f326ac3ef3cae8e06`. The page images of pp. 1–3
(PDF pages 1–3) were read.

Verbatim:

* p. 1: "Theorem A. If `E/ℚ` is an elliptic curve, then `E` is modular."
* p. 1: "If `N` is a positive integer then we let `Γ₁(N)` denote the subgroup of `SL₂(ℤ)`
  consisting of matrices that modulo `N` are of the form `(1 ∗; 0 1)`. [...] Recall that a cusp
  form of weight `k ≥ 1` and level `N ≥ 1` is a holomorphic function `f` on the upper half
  complex plane `𝔥` such that • for all matrices `(a b; c d) ∈ Γ₁(N)` and all `z ∈ 𝔥`, we have
  `f((az + b)/(cz + d)) = (cz + d)^k f(z)`; • and `|f(z)|² (Im z)^k` is bounded on `𝔥`. The space
  `S_k(N)` of cusp forms of weight `k` and level `N` is a finite dimensional complex vector
  space. If `f ∈ S_k(N)` then it has an expansion `f(z) = ∑_{n=1}^∞ c_n(f) e^{2πinz}` and we
  define the L-series of `f` to be `L(f, s) = ∑_{n=1}^∞ c_n(f)/n^s`."
* p. 2: "For each prime `p ∤ N` there is a linear operator `T_p` on `S_k(N)` defined by
  `(f|T_p)(z) = p^{−1} ∑_{i=0}^{p−1} f((z + i)/p) + p^{k−1} (cpz + d)^{−k} f((apz + b)/(cpz + d))`
  for any `(a b; c d) ∈ SL₂(ℤ)` with `c ≡ 0 mod N` and `d ≡ p mod N`. The operators `T_p` for
  `p ∤ N` can be simultaneously diagonalised on the space `S_k(N)` and a simultaneous
  eigenvector is called an *eigenform*. If `f` is an eigenform then the corresponding
  eigenvalues, `a_p(f)`, are algebraic integers and we have `c_p(f) = a_p(f) c_1(f)`."
* pp. 2–3: "Now consider an elliptic curve `E/ℚ`. [...] Let `N(E)` denote the conductor of `E`.
  It is known that the following conditions are equivalent. (1) The L-function `L(E, s)` of `E`
  equals the L-function `L(f, s)` for some eigenform `f`. (2) The L-function `L(E, s)` of `E`
  equals the L-function `L(f, s)` for some eigenform `f` of weight 2 and level `N(E)`. [...]
  When these equivalent conditions are satisfied we call `E` modular."

The printed eigenform is a simultaneous eigenvector of the `T_p`, `p ∤ N`, only: it is not
assumed normalised, not assumed to have a nebentypus, and not assumed to be an eigenvector at the
primes dividing `N`.

## Statements (`Statement.lean`)

```lean
def IsBCDTEigenform {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Prop :=
  f ≠ 0 ∧ ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ N →
    ∃ c : ℂ, heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f = c • f

def cuspLSeries {N : ℕ} {k : ℤ} (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ (qExpansion 1 f).coeff n) s

def Condition2At (E : WeierstrassCurve ℚ) (N : ℕ) [NeZero N] : Prop :=
  ∃ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2, IsBCDTEigenform f ∧
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → E.LSeries s = cuspLSeries f s

-- PRINT
def BCDTThmAPrinted : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∃ (N : ℕ) (_ : NeZero N), Condition2At E N

def BCDTThmAPrintedAtLevel (level : WeierstrassCurve ℚ → ℕ+) : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → Condition2At E (level E : ℕ)
```

For `level = N(E)` the last is the printed statement word for word; it implies
`BCDTThmAPrinted` (`bcdtThmAPrinted_of_atLevel`).

## The proof (`Descent.lean`)

* `coeff_eq_of_eq_cuspLSeries`: for a nonzero cusp form `f` on `Γ₁(N)`, `L(E, s) = L(f, s)` on a
  right half-plane gives `c_n(f) = a_n(E)` for every `n ≥ 1` (Hecke's bound, Mathlib's
  uniqueness of Dirichlet coefficients; no growth bound for `a_n(E)` is assumed).
* `diamondOpCuspNat_eq_self_of_good`: at a prime of good reduction, a `T_p`-eigenvector with the
  coefficients of `E` is fixed by `⟨p⟩`. The Hecke coefficient formula
  `a_m(T_p f) = a_{pm}(f) + p a_{m/p}(⟨p⟩ f)` (Diamond–Shurman, Prop. 5.3.1; proved in the
  vendored library for every cusp form on `Γ₁(N)`, with no nebentypus) is compared with the
  good-prime recurrence `a_{pm}(E) = a_p(E) a_m(E) − p a_{m/p}(E)` of the Euler product.
* `diamondOpCusp_eq_self_of_eigen`: by Dirichlet's theorem (Mathlib,
  `Nat.forall_exists_prime_gt_and_eq_mod`) every unit modulo `N` is the class of a prime of good
  reduction prime to `N`; so every diamond operator fixes `f`, i.e. the nebentypus is trivial.
* `isModular_of_condition2At`, `bcdtThmA_of_printed`, `bcdtThmA_of_printedAtLevel`: `f` lies in
  `S₂(Γ₁(N), 1)`, which is `S₂(Γ₀(N))` with the same function, so it witnesses
  `PoleS12.IsModular E` at the same level.

## Faithfulness (`Dictionary.lean`, `Literal.lean`, `Examples.lean`)

* `heckeTCuspNat_apply_eq_printed`: the vendored `T_p` is the printed formula, for every
  admissible `(a b; c d)`.
* `isPrintedCuspForm_iff`: for `k ≥ 1`, a function is a printed cusp form (holomorphic,
  printed transformation law on `Γ₁(N)`, `|f(z)|² (Im z)^k` bounded) iff it is a Mathlib cusp
  form on `Γ₁(N)`.
* `coeff_prime_eq_eigenvalue_mul_coeff_one`: the printed `c_p(f) = a_p(f) c_1(f)`.
* `condition2At_iff`: for an eigenform, the half-plane equality of L-functions is equivalent to
  `c_n(f) = a_n(E)` for all `n ≥ 1`; `condition2At_normalised_eigen`: the eigenform of condition
  (2) is normalised and has eigenvalue `a_p(E)` at every `p ∤ N` (neither is assumed).
* `bcdtThmAPrintedLiteral_iff`: the statement written with the printed definitions themselves
  (`IsPrintedCuspForm`, `printedHeckeT`, `IsPrintedEigenform`, the printed expansion
  `IsPrintedExpansion`) is equivalent to `BCDTThmAPrinted`; `bcdtThmA_of_printedLiteral`.
* Non-vacuity: `isBCDTEigenform_of_eigenform`, `isBCDTEigenform_of_newform`,
  `not_isBCDTEigenform_zero`; the discriminant is an eigenform of weight 12 and level 1
  (`isBCDTEigenform_discriminant`, `isPrintedEigenform_discriminant`).

## Consumers (`Cite.lean`)

* `kolyvaginRankOne_of_bcdtPrinted`: `PoleS12.kolyvaginRankOne_of_printed` with the print.
* `modularNewform_of_bcdtPrinted`: `PrintsAnalytic.modularNewform_of_printed`, unchanged, with
  the print in place of `PoleS12.BCDTThmA`.

## What remains

* The print itself, `BCDTThmAPrinted`, is the only input (a proposition, not an axiom).
* The level of the print is the conductor `N(E)`. It is not formalized: the library has no
  conductor of an elliptic curve. `BCDTThmAPrintedAtLevel` takes the level as a parameter, so a
  future conductor makes the statement literal without changing the proof.
