# coeff-ext (2026-11-16)

**Result.** The two coefficient-field dictionary steps are gone. `dsThm965Weak` and `dsThm966` are proved in
Lean from leaves stated as printed. `ZInQKernel/Contrib/OneProof/DSCoeffExt.lean` compiles with no sorry and only
the standard axioms. Report: `docs/research/coeff-ext.md`.

* `dsThm965Weak_of_printed : DSThm965Printed → EigenformCoeffFieldFinite → DS965Weak.DSThm965Weak`.
  `DSThm965Printed` is Diamond–Shurman 9.6.5 over `GL₂(K_{f,λ})`, with `K_{f,λ}` Mathlib's
  `λ.adicCompletion K_f` and `λ` a prime of `𝓞_{K_f}` over `ℓ`. It keeps the "charpoly ∨ satisfies"
  disjunction. The extension to every `ιC`, `ιL` is proved: `τ = ιL ∘ ιC⁻¹`, the place `λ_τ`, continuity, the
  continuous extension `K_{f,λ_τ} → ℚ̄_ℓ`, and `charpoly_map`.
* `EigenformCoeffFieldFinite` (`K_f` is a number field) is a new leaf. The print presupposes it, and the field
  quantifies over all eigenforms, so it cannot be avoided. Printed for `k = 2` (DS 6.5.1); for general `k`
  it rests on Shimura 1971 Thm 3.52 + §3.5. Locators UNVERIFIED.
* `dsThm966_of_printed`, with a proved converse: `DSThm966Printed` is `DSThm966` with Diamond–Shurman's
  "normalized eigenform", located at Deligne–Serre 1974 Thm 4.1 (4.1.1), p. 514.
* `isNormalizedEigenform_iff_DS`: Diamond–Shurman Def. 5.8.1, over Tau Ceti's `Eigenform` with `a₁ = 1`, is
  equivalent to the kernel's coefficient form. The `U_p` part (`p ∣ N`) is new.
* `#discharges` shows both fields discharged (`scratch/coeff-ext/discharges-output.txt`).
* Autofold spec `scratch/coeff-ext/autofold.json`. Dry run: GLUE unchanged (strict and strictest 34/11 → 35/11),
  and the generated fold compiles.
* dsThm966's locator now reads Deligne–Serre in the six docstrings named in the brief. The edits are
  comment-only, and the four files each recompile.

**What remains.** The page checks of DS 9.6.5, DS 6.5.1 / Shimura 3.52 and Deligne–Serre 4.1 (no network). The
locators.md rows (listed in the report, §7) and the actual fold are for the integrator.
