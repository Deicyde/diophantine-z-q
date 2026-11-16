# coeff-ext: Diamond–Shurman 9.6.5 over `K_{f,λ}`, and the normalized-eigenform dictionary

Task coeff-ext (2026-11-16), base origin/main 2880fef1. Scratch: `scratch/coeff-ext/` (log `log.md`).
Contribution: `ZInQKernel/Contrib/OneProof/DSCoeffExt.lean` (namespace `DSCoeffExt`).

## 1. Result

**Both coefficient-field dictionary steps are gone, and the two fields are proved in Lean from leaves in their
printed form.** VERIFIED: compiled, `#discharges`, axioms `propext`, `Classical.choice`, `Quot.sound`.

```lean
theorem DSCoeffExt.dsThm965Weak_of_printed (h1 : DSCoeffExt.DSThm965Printed)
    (h2 : DSCoeffExt.EigenformCoeffFieldFinite) : DS965Weak.DSThm965Weak
theorem DSCoeffExt.dsThm966_of_printed (h : DSCoeffExt.DSThm966Printed) : ZInQ.Contrib.HodgeSplit.DSThm966
theorem DSCoeffExt.isNormalizedEigenform_iff_DS :
    ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ ↔ DSCoeffExt.IsNormalizedEigenformDS g χ
```

`#discharges` output (`scratch/coeff-ext/discharges-output.txt`, VERIFIED):

```
DISCHARGES [OpenResearchLeaves26.dsThm965Weak] by DSCoeffExt.dsThm965Weak_of_printed
  still assumes: [DSCoeffExt.DSThm965Printed, DSCoeffExt.EigenformCoeffFieldFinite]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.dsThm966] by DSCoeffExt.dsThm966_of_printed
  still assumes: [DSCoeffExt.DSThm966Printed]
  axioms: [propext, Classical.choice, Quot.sound]
```

* **dsThm965Weak.** The new leaf `DSThm965Printed` is Diamond–Shurman 9.6.5 as printed: a representation
  `ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})` for each prime `λ ∣ ℓ` of the number field `K_f`, with `K_{f,λ}` Mathlib's
  `λ.adicCompletion K_f`. The disjunction "characteristic polynomial ∨ satisfies" is kept, so either wording
  gives it by or-introduction. The extension to every `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`, which is what the field and
  its consumers use, is proved in Lean (§3). One more leaf comes in: `EigenformCoeffFieldFinite`, that `K_f` is a
  number field. 9.6.5 presupposes it ("with number field `K_f`"), and a field that quantifies over every
  normalized eigenform cannot be reached without it (§4).
* **dsThm966.** The new leaf `DSThm966Printed` is the old field word for word, except that "normalized
  eigenform" now has Diamond–Shurman's definition. It is located at Deligne–Serre 1974 Thm 4.1 (4.1.1),
  p. 514. It is *equivalent* to the field it replaces: `dsThm966_of_printed` and `dsThm966Printed_of_dsThm966`
  are both proved.
* **Normalized eigenform.** `IsNormalizedEigenformDS` is Diamond–Shurman's Def. 5.8.1. It is stated over Tau
  Ceti's `HeckeRing.GL2.Eigenform` (a nonzero form in the `χ`-space of the diamond operators that is an
  eigenvector of `T_n` for every `n ≥ 1`, the `U_p` for `p ∣ N` included) and asks `a₁ = 1`. It is proved
  equivalent to the kernel's coefficient form. The `U_p` part is new: `heckeTCuspNat_eq_coeff_smul_all`, for
  every prime `p`, whereas T25/Bridge.lean:56 has only `p ∤ N`.
* **Fold.** `scratch/coeff-ext/autofold.json`. Dry run: strict 34/11 on 45 → 35/11 on 46, strictest
  34/11 → 35/11. The GLUE count is unchanged; there is one more LEAF (`eigenformCoeffFieldFinite`). The
  generated fold, with line 1 stripped (`scratch/coeff-ext/FoldCheck.lean`), compiles:
  `HDec.HSyn.sixContactMin_of_open36` uses the standard axioms (VERIFIED).
* **Locator move.** dsThm966's locator now reads Deligne–Serre 1974 Thm 4.1 (4.1.1), p. 514, in the six
  docstrings named in the brief: TailS.lean:1120, TailT.lean:1531 and 1991, TailX.lean:30 and 101,
  TailZ6.lean:122. The edits are comment-only (script `scratch/coeff-ext/locator_patch.py`). TailS, TailT,
  TailX and TailZ6 were each recompiled with `lake env lean` and gave no errors.

Target met: `dsThm965Weak` and `dsThm966` are replaced by leaves stated as printed, with no dictionary step. The
remaining conventions are inherited from the old fields and listed in §5.

## 2. Statements

Targets (verbatim copies `DSThm965WeakCopy`, `DSThm966Copy` in `scratch/coeff-ext/Check.lean`, each equal to
the original by `rfl`, compiled):

* `DS965Weak.DSThm965Weak`: `ZInQKernel/Contrib/OneProof/DSThm965Weak.lean` l.56, bundle field
  `HDec.HSyn.OpenResearchLeaves26.dsThm965Weak` (TailZ41.lean l.67; its docstring at l.66 is stale: it says
  "satisfies", but the type is the disjunction). The field disappears in the fold.
* `ZInQ.Contrib.HodgeSplit.DSThm966`: TailS.lean l.1128, field `OpenResearchLeaves26.dsThm966`.

New definitions:

* `DSCoeffExt.IsNormalizedEigenformDS f χ := ∃ F : HeckeRing.GL2.Eigenform N k, F.toCuspForm = f ∧
  F.χ = MulChar.toUnitHom χ ∧ coeff f 1 = 1` (Diamond–Shurman Def. 5.8.1; Tau Ceti's `Eigenform` cites the
  same definition).
* `DSCoeffExt.coeffField f := IntermediateField.adjoin ℚ (Set.range (coeff f))`, a subfield of `ℂ`. It is the
  same definition as `coeffField` in `ZInQKernel/HDecomp/ModCurves/Defs.lean`, over the G9 copy of `coeff`.

New leaves, each with its rating:

1. **`DSThm965Printed`** (LEAF, published). Source: Diamond–Shurman, GTM 228 (2005), Thm 9.6.5 (Deligne,
   Sém. Bourbaki 355; Shimura 1971 Thm 7.14 for `k = 2`; numbering UNVERIFIED, no network). For
   `f ∈ S_k(N, χ)` a normalized eigenform (DS Def. 5.8.1), `k ≥ 2`, with `K_f` a number field, `ℓ` a prime
   and `λ : HeightOneSpectrum (𝓞 K_f)` with `ℓ ∈ λ`: there is a continuous
   `ρ : G_ℚ →* GL (Fin 2) (λ.adicCompletion K_f)` such that for `p ∤ Nℓ`, `ρ` is trivial on every inertia
   group above `p`, and for every `b ∈ K_f` with `b = χ(p)p^{k−1}`, every place `v ∣ p` of `ℚ̄` and every
   arithmetic Frobenius `σ` at `v`, `charpoly ρ(σ) = X² − a_p X + b ∨ aeval ρ(σ) (X² − a_p X + b) = 0`
   over `K_{f,λ}`.
   **Rating: printed form.** Each hypothesis is the print's ("normalized eigenform" by DS's own definition,
   "with number field `K_f`", `λ` a maximal ideal of `𝓞_{K_f}` over `ℓ`), and the coefficient field is the
   print's `K_{f,λ}` with its topology. The conclusion weakens the print in three ways only: the
   disjunction, "every `b` equal to `χ(p)p^{k−1}`", and dropping irreducibility if DS states it. Locator
   UNVERIFIED.
2. **`EigenformCoeffFieldFinite`** (LEAF, published). For a normalized eigenform `f ∈ S_k(N, χ)` (DS Def.
   5.8.1), `k ≥ 2`, `FiniteDimensional ℚ (coeffField f)`. Sources: Diamond–Shurman Thm 6.5.1 for `k = 2`;
   for every `k`, Shimura 1971 Thm 3.52 (a rational basis of `S_k(Γ₁(N))`) with the Hecke stability of that
   rational structure (§3.5). Numbers UNVERIFIED; R16Split.lean and LeafModCurves cite the same pair for
   `[K_f : ℚ] < ∞`.
   **Rating: printed form for `k = 2`. For `k ≥ 3` it is the standard statement, presupposed verbatim by
   DS 9.6.5, but I could not check where it is printed (no network).** Flagged "unread", so it counts as a
   LEAF. If a reader finds no print for general `k`, it is the composite "Shimura 3.52 + the Hecke algebra
   is a finite ℚ-algebra" and should be re-flagged "pending reading".
3. **`DSThm966Printed`** (LEAF, published). Source: Deligne–Serre, *Formes modulaires de poids 1*, Ann. Sci.
   ÉNS (4) 7 (1974), Thm 4.1, display (4.1.1), p. 514. The locator comes from the brief and I have not read
   it (UNVERIFIED). It is `DSThm966` with
   `IsNormalizedEigenformDS`.
   **Rating: printed form (a direct instance).** Deligne–Serre's hypothesis is a nonzero form of type
   `(1, χ)` that is an eigenvector of the `T_p`, `p ∤ N`, with eigenvalues `a_p`. A DS-normalized
   eigenform satisfies it, since `a₁ = 1` makes the eigenvalues the coefficients. The conclusion (continuous,
   finite image, unramified outside `N`, trace `a_p`, determinant `χ(p)`) is the old field's, unchanged.
   The old field's "reading-hold" label concerned this leaf. The only reading left open is that of
   Deligne–Serre's word "représentation linéaire" (continuous with finite image), which is unchanged from
   the old field.

## 3. The proof (all GLUE, proved in Lean)

**Dictionary (§0 of the file).** `isNormalizedEigenformDS_of` goes from the coefficient form to the DS form. It
uses Tau Ceti's `Eigenform.ofForallPrime`, which needs a `T_p`-eigenrelation at every prime.
`heckeTCuspNat_eq_coeff_smul_all` gives `T_p g = a_p g` for every prime `p`: for `p ∤ N` it is the
T25/Bridge.lean:56 argument, and for `p ∣ N` it is the same argument with `χ(p) = 0`, through Tau Ceti's
`heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul_ofUnitHom`. That criterion covers good and bad
primes alike, and at a bad prime it is the `U_p` criterion `a_{pm} = c a_m`. The nebentypus transfer is T25's
`mem_cuspFormCharSpace_of_hasNebentypus`. The converse `isNormalizedEigenform_of_DS` uses T25's
`hasNebentypus_of_mem_cuspFormCharSpace`, the divisor-sum formula
`qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0`, and
`Eigenform.qExpansion_coeff_eq_eigenvalue` (the eigenvalue of `T_n` is `a_n` when `a₁ = 1`).

**Coefficient field (§1–§6).** Fix `ℓ`, `ιC`, `ιL` and a normalized eigenform `g`. Let `K = K_g`, which is a
number field by `EigenformCoeffFieldFinite`.

1. `mem_fieldRange_of_isIntegral`: every element of `ℂ` algebraic over `ℚ` is `ιC(y)` for some `y ∈ ℚ̄`. The
   minimal polynomial splits over `ℚ̄`, and `roots_map_of_injective_of_card_eq_natDegree` applies. This gives
   the ring hom `preHom = ιC⁻¹ : K → ℚ̄` and `τ = emb = ιL ∘ ιC⁻¹ : K → ℚ̄_ℓ`.
2. `place τ`: the ideal `{a ∈ 𝓞_K : ‖τ a‖ < 1}` is a height-one prime containing `ℓ`. The facts used:
   integral elements have norm `≤ 1` (a copy of `SwanBridge.isIntegral_iff_norm_le_one`), the norm is
   ultrametric, and `‖ℓ‖ = ℓ⁻¹`.
3. `norm_le_of_valuation_le`: `v_λ(x) ≤ v_λ(y)` implies `‖τ x‖ ≤ ‖τ y‖`. Write `x/y · d = n` with
   `d ∈ 𝓞_K ∖ λ` (Mathlib's `exists_primeCompl_mul_eq_of_integer`), and use `‖τ d‖ = 1`. So `τ` is continuous
   for the `λ`-adic topology on `WithVal v_λ` (`continuous_τW`, compared with powers of `ℓ`).
4. `tgt τ = ℚ_ℓ(τ(basis of K))`. It is finite over `ℚ_ℓ`, hence complete
   (`Submodule.complete_of_finiteDimensional`), and it contains `τ(K)`. `UniformSpace.Completion.extensionHom`
   gives the continuous `τhat : K_{f,λ} → ℚ̄_ℓ` with `τhat ∘ algebraMap = τ` (`τhat_algebraMap`).
5. `mapRep`: `ρ` composed with `GL₂(τhat)`. It is continuous (`Units.continuous_map`, `Continuous.matrix_map`).
   The unramified clause transfers. The Frobenius clause transfers by `Matrix.charpoly_map`, or for the
   "satisfies" disjunct by `aeval_map_matrix` (Mathlib's `map_aeval_eq_aeval_map`). The field's `α`, `β` are
   `ιC⁻¹(a_p)` and `ιC⁻¹(a_p² − a_{p²})`, and `a_p² − a_{p²} = χ(p)p^{k−1}` by the coefficient relation
   (`coeff_sq_relation`).

## 4. Why `EigenformCoeffFieldFinite` is needed

The print's `λ` is a maximal ideal of `𝓞_{K_f}`, and Mathlib's `HeightOneSpectrum` and `adicCompletion` need
`𝓞_{K_f}` to be a Dedekind domain. So `K_f` must be a number field before the print can be applied at all.
`DSThm965Weak` quantifies over every normalized eigenform, so finiteness is needed for each of them. No existing
open leaf gives it in weight `k ≥ 3`. R16 gives it only for weight-2 newforms. The old field hid the same input
in its `∃ α : ℚ̄, ιC α = a_p` clause; its kinds.tsv flag said "the alpha clause rests on DS printing the theorem
with the number field `K_f`". That input is now a separate, named leaf.

## 5. Conventions inherited from the old fields (no coefficient-field step)

* `G_ℚ = Gal(AlgebraicClosure ℚ / ℚ)` with places as valuation subrings, where DS uses `ℚ̄ ⊂ ℂ` and maximal
  ideals of `ℤ̄`. Any isomorphism of algebraic closures transports one statement to the other. The polynomial's
  coefficients lie in `K_f ⊂ ℂ`, so `ℚ̄` does not enter them.
* `Frob_𝔭` is pkg-I4's `IsArithFrob` (arithmetic Frobenius), and "unramified" means trivial on every inertia
  group above `p`. Both are as in the old field.

## 6. Checks

* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.DSCoeffExt`
  succeeded: 13699 jobs, DSCoeffExt built in 14 s. The other modules came from a build copied from
  `~/dzq-check2`, at the same commit.
* `scratch/coeff-ext/DischargesRun.lean`: 56 open hypotheses, 2933 theorems checked; the output is above.
* `scratch/coeff-ext/Check.lean`: the verbatim copies equal the originals by `rfl`.
* The fold dry run compiles (`FoldCheck.lean`).
* After the locator edits, `lake env lean` on TailS.lean, TailT.lean, TailX.lean and TailZ6.lean (one at a
  time, against the existing oleans) gave no errors.

## 7. For the integrator

* Run `python3 scripts/one_proof/autofold.py scratch/coeff-ext/autofold.json` (it needs no `--allow-rise`).
* Rows to add to `docs/research/locators.md` (all unread; I have not read any of them):
  * `dsThm965Printed`: Diamond–Shurman GTM 228, Thm 9.6.5.
  * `eigenformCoeffFieldFinite`: Diamond–Shurman Thm 6.5.1 (`k = 2`); Shimura 1971 Thm 3.52 and §3.5.
  * `dsThm966Printed`: Deligne–Serre 1974, Ann. Sci. ÉNS (4) 7, Thm 4.1 (4.1.1), p. 514.
* The locator edits change docstrings only, so no constant hash changes.
