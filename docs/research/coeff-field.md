# coeff-field: `K_f` is a number field, reduced to the rational structure of `S_k(Γ₁(N))`

Task coeff-field (2026-11-16). Base: wip/coeff-fix 496c1f75, merged with origin/main 0caafe66 (which changed only
STATUS.md). Scratch files are in `scratch/coeff-field/` (log `log.md`). Contribution:
`ZInQKernel/Contrib/OneProof/EigenformCoeffFieldFinite.lean` (namespace `CoeffFieldFinite`, 520 lines, 28 KB).
The files `DSCoeffExt.lean` and `DSThm966EV.lean` are unchanged.

## 1. Result

**coeff-ext's leaf `DSCoeffExt.EigenformCoeffFieldFinite` is now proved in Lean from the rational structure of the
space of cusp forms. An outright proof is not possible from the tree:** neither the vendored Tau Ceti library nor
Mathlib has any rational or integral structure on spaces of modular forms of level `N > 1`. The missing input is
isolated as two `Γ₁(N)`-level printed statements. There are also two one-leaf variants. All four are proved
sufficient. VERIFIED: compiled, `#discharges` run, axioms `propext`, `Classical.choice`, `Quot.sound`.

```lean
theorem CoeffFieldFinite.eigenformCoeffFieldFinite_of_gamma1
    (hA : Gamma1IntegralSpan) (hB : DiamondIntegralToRational) : DSCoeffExt.EigenformCoeffFieldFinite
theorem CoeffFieldFinite.eigenformCoeffFieldFinite_of (hR : CharSpaceRationalSpan) : DSCoeffExt.EigenformCoeffFieldFinite
theorem CoeffFieldFinite.eigenformCoeffFieldFinite_of_numberField (hR : CharSpaceNumberFieldSpan) : ...
theorem CoeffFieldFinite.charSpaceRationalSpan_of (hA : Gamma1IntegralSpan) (hB : DiamondIntegralToRational) :
    CharSpaceRationalSpan
theorem CoeffFieldFinite.dsThm965Weak_of_printed (h1 : DSCoeffExt.DSThm965Printed)
    (hA : Gamma1IntegralSpan) (hB : DiamondIntegralToRational) : DS965Weak.DSThm965Weak
```

As a result, `dsThm965Weak` rests only on printed leaves: Diamond–Shurman 9.6.5 as printed (coeff-ext's
`DSThm965Printed`), Shimura's integral basis of `S_k(Γ₁(N))`, and the rationality of the diamond operators.
The `k = 2` restriction does not apply: coeff-fix §1 showed that the consumers need every `k ≥ 2`, and all the
leaves here are stated for every `k ≥ 2`.

`#discharges` (`scratch/coeff-field/discharges-output.txt`; the full output is in `discharges-full.txt`):

```
DISCHARGES [OpenResearchLeaves26.dsThm965Weak] by CoeffFieldFinite.dsThm965Weak_of_printed
  still assumes: [DSCoeffExt.DSThm965Printed,
 CoeffFieldFinite.Gamma1IntegralSpan,
 CoeffFieldFinite.DiamondIntegralToRational]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.dsThm965Weak] by CoeffFieldFinite.dsThm965Weak_of_printed_charSpace
  still assumes: [DSCoeffExt.DSThm965Printed, CoeffFieldFinite.CharSpaceRationalSpan]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.dsThm965Weak] by CoeffFieldFinite.dsThm965Weak_of_printed_numberField
  still assumes: [DSCoeffExt.DSThm965Printed, CoeffFieldFinite.CharSpaceNumberFieldSpan]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 56 open hypotheses, 2991 theorems checked, 12 discharge one
```

## 2. The new leaves and their ratings

Every locator below is from memory. No source was read (no network), so all are UNVERIFIED.

### 2.1 `Gamma1IntegralSpan` (main route)

```lean
def CoeffFieldFinite.Gamma1IntegralSpan : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ), 2 ≤ k →
    Submodule.span ℂ {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = z} = ⊤
```

**LEAF, printed form.** Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971),
Thm 3.52: `S_k(Γ₁(N))` has a basis of forms whose Fourier coefficients are rational integers. Other sources:
Diamond–Im 1995 §12.3, and Diamond–Shurman §6.5 for `k = 2`. A basis spans, so the leaf is a consequence of
the print. It is used only for `k ≥ 2`.

The objects are all Mathlib's: `CuspForm` on `Γ₁(N)` (Mathlib's `Gamma1`, the matrices `≡ (1 *; 0 1) mod N`,
the same group as Shimura's), and `qExpansion 1`, the expansion in `q = e^{2πiτ}` at `∞`, which is Shimura's
Fourier expansion. The leaf is not vacuous. For example, for `S_2(Γ₁(1)) = 0` it holds trivially, and in
general it is the classical theorem.

### 2.2 `DiamondIntegralToRational` (main route)

```lean
def CoeffFieldFinite.DiamondIntegralToRational : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k), 2 ≤ k →
    (∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = z) →
    ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 (diamondOpCusp k d g)).coeff n = q
```

**LEAF, printed form (a weakening of the print).** The source statement is that the Hecke algebra
`𝕋_ℤ = ℤ[T_n, ⟨d⟩]` preserves `S_k(Γ₁(N), ℤ)`: Diamond–Im 1995 §12.3–12.4; Shimura 1971 §3.5 with Thm 3.52;
Diamond–Shurman §6.5 for `k = 2`. Geometrically, `⟨d⟩` is an automorphism over `ℚ` of the `μ_N`-model of
`X₁(N)` that fixes the rational cusp `∞`, so it commutes with the `q`-expansion principle.

The leaf keeps only the `⟨d⟩` part, with integral input and rational output. It therefore follows from the
print whether the print states stability of `S_k(Γ₁(N), A)` for `A = ℤ`, `ℤ[1/N]` or `ℚ`. `diamondOpCusp k d`
is Tau Ceti's diamond operator: slash by any `γ ∈ Γ₀(N)` whose lower-right entry is `≡ d (mod N)`
(`coe_diamondOpCusp`, DiamondOperators.lean:238). That is the classical `⟨d⟩`. The leaf quantifies over all
`d`, so the `d` versus `d⁻¹` convention does not matter.

**Reading risk.** A source might define `𝕋_ℤ` without the diamond operators, or prove stability only for the
`T_n`. In that case the leaf is the printed consequence "`⟨d⟩` is defined over `ℚ`", which needs its own
locator.

### 2.3 One-leaf variants

* `CharSpaceRationalSpan`: for `k ≥ 2`, `S_k(Γ₁(N), χ)` (Tau Ceti's `cuspFormCharSpace k χ`, the joint
  eigenspace `⟨d⟩ f = χ(d) f`) is spanned over `ℂ` by forms whose coefficients lie in `ℚ(χ)` (`charField χ`,
  the field `IntermediateField.adjoin ℚ (range χ)`). This is attributed to Shimura 1971 Thm 3.52 / §3.5 and to
  Diamond–Im §12.3–12.4 in the form "`S_k(N, χ)` has a basis with coefficients in `ℤ[χ]` (or `ℚ(χ)`)"
  (UNVERIFIED). In Lean it follows from the two leaves above (`charSpaceRationalSpan_of`).
* `CharSpaceNumberFieldSpan`: the same with "coefficients in some number field `L ⊆ ℂ`". This is the weakest
  form, and every printed variant (`ℤ[χ]`, `ℚ(χ)`, `ℚ(ζ_N)`) implies it.

Each is one leaf in place of `EigenformCoeffFieldFinite`, so the leaf count does not change. The main route
uses two leaves because its two statements are the classical `Γ₁(N)`-level prints.

### 2.4 Why the diamond input cannot be dropped

With only `Gamma1IntegralSpan`, the operators that visibly preserve rational `q`-expansions on `S_k(Γ₁(N))` are
the `U_p` for `p ∣ N` and the `T_p` for `p ≡ 1 (mod N)`. The other `T_p` involve `a_{n/p}(⟨p⟩g)` in their
coefficient formula. Those operators do not determine `f`. If `ψ` is a character mod `N`, the twist `f ⊗ ψ`
has the same `a_p` for every `p ≡ 1 (mod N)`, and it can lie in the same space with a different nebentypus.
So some statement linking the `⟨d⟩` to the rational structure is needed (SPECULATIVE: no proof that every route
needs it, but the standard ones all use it).

## 3. The glue (all proved, `EigenformCoeffFieldFinite.lean`)

1. **Abstract linear algebra** (`finiteDimensional_adjoin_eigenvalues`). Setting: `V` finite-dimensional over a
   field `K`, `F → K` a field extension, `c_i : V →ₗ[K] K` with zero joint kernel, and
   `W = {v | ∀ i, c_i v ∈ F}` spanning `V` over `K`. Let `f ≠ 0`, and let every `μ ∈ s` be the eigenvalue at
   `f` of a `K`-linear `T` that preserves `W`. Then `FiniteDimensional F (Algebra.adjoin F s)`. The proof:
   * finitely many `c_i` separate points (the span of the `c_i` in the finite-dimensional dual is finitely
     generated);
   * so `W` embeds `F`-linearly in `F^m` (`finiteDimensional_ratPart`);
   * the operators preserving `W` that have `f` as an eigenvector form an `F`-subalgebra (`stab`) of
     `End_K V`. It embeds in `End_F W`, because `W` spans `V` over `K`;
   * the eigencharacter `stab →ₐ[F] K` (`lam`) has finite-dimensional range, which contains `s`.
2. **Hecke stability on `S_k(N, χ)`** (`hecke_coeff_mem`). Tau Ceti's coefficient formula
   `a_m(T_n F) = Σ_{d ∣ (m,n)} χ(d) d^{k−1} a_{mn/d²}(F)` (CoefficientFormula.lean:115, all `n ≥ 1`, the `U_p`,
   `p ∣ N`, included) keeps the coefficients in any field `L ⊇ ℚ(χ)`. The values `χ(d)` are `0` or values of
   `χ` (`ofUnitHom_mem_charField`).
3. **Eigenvalues are coefficients.** For a full Tau Ceti eigenform with `a₁ = 1`, `a_n = λ_n`
   (`Eigenform.qExpansion_coeff_eq_eigenvalue`), and `a₀ = 0`. So `K_f ⊆` a finite-dimensional
   `L`-algebra. `L = L₀ ⊔ ℚ(χ)` is a number field (`ℚ(χ)` is generated by roots of unity), so the algebra is
   finite over `ℚ`. Then `K_f.toSubalgebra = Algebra.adjoin ℚ (range a)`, since the coefficients are algebraic.
4. **The `χ`-projector** (`proj = Σ_d χ(d⁻¹) ⟨d⟩`). It maps `S_k(Γ₁(N))` into `S_k(N, χ)` (`proj_mem`, by
   reindexing `d ↦ ed`), and it is `φ(N)·id` on `S_k(N, χ)` (`proj_of_mem`). With `DiamondIntegralToRational`,
   it sends integral forms to `ℚ(χ)`-rational forms (`proj_coeff_mem`). So `S_k(N, χ) = proj(span ℤ-forms)`
   is spanned by `ℚ(χ)`-rational forms (`charSpaceRationalSpan_of`).

Lean pitfalls (VERIFIED):

* `group` does not use commutativity. In `(ZMod N)ˣ`, finish with
  `simp only [zpow_neg_one]; rw [mul_comm e, mul_inv_cancel_right]`.
* `map_smul' := fun _ _ => rfl` for `ℚ`-linear maps between subalgebras of `ℂ` (`Algebra.adjoin L s` with
  `L` an intermediate field) gave a kernel deterministic timeout. `Subtype.ext (by simp)` fixes it.
* `CuspForm` has `Module ℂ` only, not a general `Module L`. The abstract lemma therefore puts the `F`-module
  structure on `V` inside its proof with `Module.compHom`, and its statement does not mention it.

## 4. Checks

* `lake env lean ZInQKernel/Contrib/OneProof/EigenformCoeffFieldFinite.lean`: compiles, no warnings, about
  15 s. A copy is at `scratch/coeff-field/EigenformCoeffFieldFinite.lean`. The development files
  `scratch/coeff-field/Abstract.lean`, `Spec.lean` and `SpecTest.lean` (with `#print axioms`) also compile.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.EigenformCoeffFieldFinite`
  succeeded (13700 jobs; build tree copied from coeff-fix; `scratch/coeff-field/build.log`).
  `ZInQ.OneProof.frozenTarget` uses only the standard axioms.
* `#discharges` (`scratch/coeff-field/DischargesRun.lean`): the output is in §1.
* **Autofold** (`scratch/coeff-field/autofold.json`). It supersedes `scratch/coeff-fix/autofold.json`:
  * dsThm965Weak comes from `dsThm965Printed`, `gamma1IntegralSpan` and `diamondIntegralToRational`;
  * dsThm966 is unchanged from coeff-fix;
  * the one-leaf alternatives are listed in the spec's note.

  The dry run (`autofold-dryrun.txt`) gives strict 34/11 on 45 → 36/11 on 47, and the same for strictest.
  GLUE is unchanged; coeff-fix's spec gave 35/11 on 46. The generated module, with line 1 stripped
  (`FoldCheck.lean`), compiles: `HDec.HSyn.sixContactMin_of_open36` uses only the standard axioms.
* No numerical check was run. `~/pyenv` (PARI/cypari2) does not exist on this host, and the system `python3`
  has no cypari2.

## 5. For the integrator

* Fold with `python3 scripts/one_proof/autofold.py scratch/coeff-field/autofold.json` instead of coeff-fix's
  spec. To fold one leaf in place of `EigenformCoeffFieldFinite`, use the proof
  `_root_.CoeffFieldFinite.dsThm965Weak_of_printed_numberField {n}.dsThm965Printed {n}.charSpaceNumberFieldSpan`
  instead (the count is then that of coeff-fix).
* Proposed rows for locators.md (all unread):
  * `gamma1IntegralSpan`: Shimura 1971, Thm 3.52 (integral basis of `S_k(Γ₁(N))`).
  * `diamondIntegralToRational`: Diamond–Im 1995 §12.3–12.4, the `⟨d⟩` part of "`𝕋_ℤ` preserves
    `S_k(Γ₁(N), ℤ)`" (also Shimura 1971 §3.5; Diamond–Shurman §6.5 for `k = 2`).
  * `charSpaceRationalSpan` / `charSpaceNumberFieldSpan`: Shimura 1971 Thm 3.52 / §3.5, or Diamond–Im §12.3,
    for `S_k(N, χ)` over `ℤ[χ]`.
* `DSCoeffExt.EigenformCoeffFieldFinite` is no longer a leaf of any route offered here. Its row (coeff-ext,
  coeff-fix) is replaced by the rows above.

## 6. What remains

* Page checks (no network): Shimura 1971 Thm 3.52 (whether it covers `Γ₁(N)` with integer coefficients, or
  `S_k(N, χ)` with `ℚ(χ)` coefficients), and the location of the diamond-stability statement (Diamond–Im §12.3–12.4
  or Shimura §3.5).
* Proving either leaf in Lean would need the `q`-expansion principle, Eichler–Shimura (integral homology), or a
  spanning set of forms with rational coefficients at level `N`. None of these is in Mathlib, Tau Ceti or the
  other vendored libraries; Mathlib has the level-one ring `ℂ[E₄, E₆]` only.
