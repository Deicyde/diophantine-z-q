# coeff-rational (2026-11-16)

**Result.** main's open field `eigenformCoeffFieldFinite` (`K_f = ℚ(a_n(f))` is a number field for a normalized
eigenform of weight `k ≥ 2`; strict GLUE, kind composite) is proved in Lean from two printed-form leaves on
`S_k(Γ₁(N))`, with no diamond-operator leaf. The autofold dry run gives strict **16/21 → 18/20 (GLUE −1)**, and the
same for strictest. `ZInQKernel/Contrib/OneProof/CoeffRational.lean` compiles with no warnings and only the
standard axioms. Report: `docs/research/coeff-rational.md`.

* **Narrowing is impossible** (VERIFIED, read in the source). The field reaches `R14`/`R13` via `dsThm965Weak`. They
  are applied in `G0Galois.g12` (TailA:2211, from TailD:137 and TailK:394) at the eigenform that Pan∘Berger
  attaches to `r₅`. That eigenform's level, character and weight are arbitrary, and it is used to rule out `k ≥ 3`.
  Nothing in the tree makes its coefficients rational. `r16CoreY` gives `K_f` finite only for weight-2 newforms.
* **No outright proof**: no library has a `ℚ`-structure on `S_k(Γ₁(N))`, `N > 1`. Mathlib has level-one Eisenstein
  `q`-expansions only, and Tau Ceti has only the Sturm bound and complex conjugation. A fixed-level basis does not
  apply, because `N` and `k` are arbitrary.
* **New leaf** `CoeffRational.HeckePrimeIntegralToRational`. The double-coset operator `T_p`
  (`Γ₁(N) diag(1,p) Γ₁(N)`, `p ∤ N`) maps integral `q`-expansions to rational ones. Rated printed form: it is the
  `T_p` part of "the `T_n` preserve `S_k(Γ₁(N), ℤ)`" (Shimura 1971 §3.5 / Thm 3.52; Diamond–Im §12.3–12.4;
  locators UNVERIFIED). It sits with coeff-field's `Gamma1IntegralSpan` (Shimura Thm 3.52) and replaces
  coeff-field's `DiamondIntegralToRational`, which had a reading risk and now follows from it.
* **Glue proved:**
  * `⟨d⟩ = ⟨p⟩` for a prime `p ≡ d (mod N)` (Mathlib's Dirichlet theorem);
  * `a_n(⟨p⟩g) = p^{1−k}(a_{pn}(T_p g) − a_{p²n}(g))`, from Tau Ceti's recurrence;
  * then coeff-field's `χ`-projector and eigenvalue lemma.
* **One-leaf alternative** `RationalHeckeSpan`: `S_k(Γ₁(N))` is spanned by forms `g` with `g` and every `T_p g`
  rational. It is the common weakening of both pairs. It is composite, and the count is unchanged.
* **Checks:**
  * `#discharges`: `eigenformCoeffFieldFinite` is discharged by `CoeffRational.eigenformCoeffFieldFinite_of_heckePrime`,
    still assuming `[Gamma1IntegralSpan, HeckePrimeIntegralToRational]`, and by `_of_rationalHeckeSpan`. Both use the
    standard axioms.
  * Main and Discharges build.
  * `scratch/coeff-rational/autofold.json`; the `FoldCheck.lean` (`sixContactMin_of_open39`) compiles.

**What remains.** Page checks of Shimura 1971 Thm 3.52 / §3.5 and of Diamond–Im §12.3–12.4, including the `T_p`
convention, `diag(1,p)`. If one statement prints the integral basis together with its Hecke stability,
`RationalHeckeSpan` is printed form and the one-leaf fold also gives −1. The fold itself and the locators.md rows
are left to the integrator. An outright proof would need the `q`-expansion principle or Eichler–Shimura over `ℤ`.
