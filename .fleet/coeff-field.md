# coeff-field (2026-11-16)

**Result.** coeff-ext's leaf `DSCoeffExt.EigenformCoeffFieldFinite` (`K_f = ℚ(a_n(f))` is a number field for a
normalized eigenform of weight `k ≥ 2`) is now proved in Lean from the rational structure of `S_k(Γ₁(N))`. It
cannot be proved outright from the tree: Mathlib and the vendored libraries have no rational or integral
structure on modular forms of level `N > 1`. As a result, `dsThm965Weak` rests only on printed leaves.
`ZInQKernel/Contrib/OneProof/EigenformCoeffFieldFinite.lean` compiles with no sorry and only the standard
axioms. Report: `docs/research/coeff-field.md`.

* **New leaves** (all rated printed form; locators UNVERIFIED, no network):
  * `CoeffFieldFinite.Gamma1IntegralSpan`: `S_k(Γ₁(N))` is spanned by forms with integer `q`-expansions
    (Shimura 1971 Thm 3.52).
  * `CoeffFieldFinite.DiamondIntegralToRational`: `⟨d⟩` (Tau Ceti's `diamondOpCusp`) sends integral
    `q`-expansions to rational ones. This is the `⟨d⟩` part of "`𝕋_ℤ` preserves `S_k(Γ₁(N), ℤ)`", from
    Diamond–Im 1995 §12.3–12.4.
  * One-leaf variants: `CharSpaceRationalSpan` (`S_k(N, χ)` is spanned by `ℚ(χ)`-rational forms) and the weakest
    form, `CharSpaceNumberFieldSpan` (coefficients in some number field).
* **Glue, all proved:**
  * an abstract lemma: eigenvalues of operators that preserve a spanning `F`-structure generate a
    finite-dimensional `F`-algebra;
  * Hecke stability of `ℚ(χ)`-rationality on `S_k(N, χ)`, from Tau Ceti's coefficient formula, all `T_n`,
    the `U_p` included;
  * `a_n = λ_n` for eigenforms with `a₁ = 1`;
  * the `χ`-projector `Σ χ(d⁻¹)⟨d⟩`, which builds the `ℚ(χ)`-structure of `S_k(N, χ)` from the two
    `Γ₁(N)` leaves.
* **`#discharges`:** dsThm965Weak is discharged by `CoeffFieldFinite.dsThm965Weak_of_printed`, which still
  assumes `[DSThm965Printed, Gamma1IntegralSpan, DiamondIntegralToRational]`. The variants `_charSpace` and
  `_numberField` assume one leaf each. All use only the standard axioms
  (`scratch/coeff-field/discharges-output.txt`). The build of Main + Discharges + the contribution succeeded.
* **Autofold:** the spec `scratch/coeff-field/autofold.json` supersedes coeff-fix's spec (dsThm966 is
  unchanged). The dry run gives 34/11 on 45 → 36/11 on 47 (strict and strictest), so GLUE is unchanged.
  `FoldCheck.lean` compiles. The one-leaf alternative gives coeff-fix's count.

**What remains.** Page checks of Shimura 3.52 and of the diamond-stability print (Diamond–Im §12.3–12.4). To
prove either leaf in Lean would need the `q`-expansion principle or Eichler–Shimura, which are not in any
library. The locators.md rows and the fold are left to the integrator. No PARI check was run, because cypari2
is not installed on this host.
