# gz-moduli: `GrossZagierFormulaCd` from the Gross–Zagier formula in its printed moduli form

Status: research note (task gz-moduli, 2026-11-16), branch `wip/gz-moduli` (base 60a3fac7 with wip/gz-weil ad22e947
merged). Lean: `ZInQKernel/Contrib/OneProof/GrossZagierModuli.lean` (new, 47 KB) and
`ZInQKernel/Contrib/OneProof/GrossZagierModuli/NonVacuous.lean` (new). Nothing else under `ZInQKernel/` was edited.
Scratch and log: `scratch/gz-moduli/`.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published theorem with an
exact reference. **SPECULATIVE**: an assessment. This host has no network and no copy of Gross–Zagier, Gross 1984 or
Shimura 1971: **every theorem number, locator and constant of the literature below is UNVERIFIED** (from memory).

---

## 0. Main result

**`GZHL3.GrossZagierFormulaCd` is proved in Lean from one new printed leaf, the Gross–Zagier formula in its moduli
form. No other hypothesis is used.**

```lean
theorem ZInQ.GZModuli.grossZagierFormulaCd_of_moduli (h : ZInQ.GZModuli.GrossZagierModuliCd) :
    ZInQ.GZHL3.GrossZagierFormulaCd
```

The proof is for every elliptic curve, not only `C_d`:
`grossZagierFormulaAt_of_moduli (E) [E.IsElliptic] : GrossZagierModuliAt E → GZHL3.GrossZagierFormulaAt E` and
`grossZagierFormula_of_moduli : GrossZagierModuli → GZHL3.GrossZagierFormula`. The `C_d` leaf is the restriction of
the general one (`grossZagierModuliCd_of`).

* Axioms: `[propext, Classical.choice, Quot.sound]` for every theorem listed (VERIFIED, `scratch/gz-moduli/Check.lean`,
  output `out_check.txt`).
* In the new leaf the Heegner points are **moduli points**: cyclic `N`-isogenies `E₁ → E₂` with
  `End E₁ = End E₂ = 𝒪_D`, given in the lattice model of complex elliptic curves. The modular parametrization is an
  **algebraic morphism `φ : X₀(N) → E` over `ℚ`**: a point of `E(ℚ(X₀(N)))`, where `ℚ(X₀(N))` is the field of the
  canonical model. The analytic objects of the old leaf (newform `f`, period lattice `L`, `c`, `PeriodsIn`, the
  Eichler integral, Heegner forms) no longer appear in it, except `f` as the newform whose L-function is `L(E, s)`.
* Proved in this task:
  - the analytic parametrization `τ ↦ weierPt E L (c φ_f(τ))` is such a `φ` (`isModularParam_of`);
  - its value at every point agrees with the moduli definition (`modPt_eq`);
  - the lattice pairs `(⟨1, τ_Q⟩, ⟨1/N, τ_Q⟩)` of a complete set of Heegner forms of residue `β` are a complete set of
    representatives of the moduli Heegner points with `𝔫 = (N, (−β + √D)/2)` (`isHeegnerPointReps_of`). The
    classification of Heegner points (every one is such a pair) is proved here.

**Effect on the counts.** `GrossZagierFormulaCd` (kind consequence, GLUE under the statement review of 2026-11-15)
becomes `GrossZagierModuliCd` (published, printed form with the constant forgotten, flagged unread): **−1 strict GLUE,
no new glue.** Together with gz-heegner (`HeegnerPointRationalCd` from `hCM` and `X0ModuliGaloisMero`), `hL3` is
replaced by three hypotheses (`scratch/gz-moduli/MainEdit.lean`, `frozenTarget_gzmoduli`, compiled):

| Hypothesis | Kind | Status |
| --- | --- | --- |
| `GZHeegner.X0ModuliGaloisMero` | consequence (the printed form of the canonical-model theorem, as `hX` was) | GLUE |
| `GZModuli.GrossZagierModuliCd` | published (this task) | LEAF |
| `GZHL3.GrossConjugationCd` | published (gz-hl3), moduli form in gz-conj | LEAF |

So `hL3` (1 composite GLUE) becomes 1 consequence GLUE plus 2 leaves: neutral in GLUE outside H, and **−1 once
X0ModuliGaloisMero is rated printed or replaced**. `X0ModuliGaloisMero` was outside this task.

**Not needed: GAGA.** The task suggested producing the algebraic `φ` for `C_d` from `ShimuraCMParamCd` with the field
`gagaMorphism`. In the formulation used here a `ℚ`-morphism `X₀(N) → E` is a pair of functions in `ℚ(X₀(N))`
satisfying the Weierstrass equation, and gz-heegner has already proved (§8–§9 of `Heegner.lean`) that the coordinates
of the analytic parametrization have the defining properties of `ℚ(X₀(N))`: meromorphy on `ℍ`, moderate growth at
every cusp and rational `q`-expansions. So no comparison theorem between analytic and algebraic maps is used.
`gagaMorphism` (as stated in the kernel) is about homomorphisms of abelian varieties; it would not apply to the curve
`X₀(N)` anyway.

---

## 1. The new leaf

`ZInQ.GZModuli.GrossZagierModuliAt E` (`GrossZagierModuli.lean` §1), in words. Let:

* `E/ℚ` be an elliptic curve, and `f` a newform of level `N` and trivial character with `aₙ(f) = aₙ(E)`;
* `φ = (X, Y)` satisfy `IsModularParam N E X Y`, i.e. `φ : X₀(N) → E` is a nonconstant morphism over `ℚ` with
  `φ(∞) = O`;
* `D < −4` be an odd fundamental discriminant with the Heegner hypothesis, and `β² ≡ D (mod 4N)`;
* `τ : R → ℍ` satisfy `IsHeegnerPointReps N D β τ`: a complete set of representatives of the Heegner points `x` of
  discriminant `D` with `𝔫 = (N, (−β + √D)/2)`;
* `K = ℚ(δ)`, `δ² = D`, be embedded in `ℂ` by `ι(δ) = i√|D|`, and `y ∈ E(K)` satisfy `ι(y) = Σ_r φ(τ_r)`
  (this is `y_K`);
* `F`, `G` be the entire continuations of `L(f, s)` and `L(f ⊗ χ_D, s)`.

Then `L'(E/K, 1) = (F G)'(1) = κ · ĥ(y)` for some real `κ > 0`.

The objects (all genuine: Mathlib's `Submodule ℤ ℂ`, `PeriodPair`-free; gz-heegner's `IsRatModFnMero`, `RegularAt`):

| Lean | Meaning |
| --- | --- |
| `cmOrder D` | `𝒪_D = ℤ + ℤ(D + √D)/2 ⊂ ℂ`, `√D = i√|D|` |
| `latEnd Λ` | `End(ℂ/Λ) = {α : αΛ ⊆ Λ}` |
| `IsCLattice Λ` | `Λ = ℤω₁ + ℤω₂`, `ω₂/ω₁ ∈ ℍ` |
| `IsHeegnerPair N D β Λ₁ Λ₂` | `ℂ/Λ₁ → ℂ/Λ₂` (`z ↦ z`) has kernel `Λ₂/Λ₁` cyclic of order `N` (`Λ₂ = Λ₁ + ℤv`, `kv ∈ Λ₁ ⇔ N ∣ k`); `End(Λ₁) = End(Λ₂) = 𝒪_D`; `(−β + √D)/2 · Λ₂ ⊆ Λ₁` |
| `Homothetic P P'` | `P' = μP`, `μ ∈ ℂ^×` (isomorphism of isogenies) |
| `pairOf N τ` | `(⟨1, τ⟩, ⟨1/N, τ⟩)`: the point `τ` of `Y₀(N)` as the pair `(ℂ/⟨1, τ⟩, ⟨1/N⟩)` |
| `IsHeegnerPointReps N D β τ` | each `pairOf N (τ r)` is a Heegner pair, no two are homothetic, every Heegner pair is homothetic to one of them |
| `IsModularParam N E X Y` | `X, Y ∈ ℚ(X₀(N))` (`IsRatModFnMero`), the Weierstrass equation where both are regular, `‖X‖ → ∞` at `i∞` |
| `modPt E X Y τ` | `(x₀, y₀)` if `X → x₀`, `Y → y₀` on a punctured neighbourhood of `τ` (and `(x₀, y₀)` is on `E`); else `O` |

Why these are faithful (STANDARD facts, references UNVERIFIED):

* **Elliptic curves over `ℂ` and their isogenies.** Every elliptic curve over `ℂ` is `ℂ/Λ`, and
  `Hom(ℂ/Λ, ℂ/Λ') = {α ∈ ℂ : αΛ ⊆ Λ'}` (Silverman AEC VI.4–VI.5; Serre, *Cours d'arithmétique* VII). A cyclic
  `N`-isogeny is then, up to isomorphism, `ℂ/Λ₁ → ℂ/Λ₂` with `Λ₂/Λ₁ ≅ ℤ/N`. The cyclicity condition is stated
  elementwise (a generator `v` of exact order `N`), which is equivalent.
* **Heegner points.** Gross–Zagier Ch. II §1 and Gross 1984 §1–§2 define a Heegner point of discriminant `D` as a
  cyclic `N`-isogeny `E₁ → E₂` with `End E₁ = End E₂ = 𝒪_D`. It is determined by `(𝒪_D, 𝔫, [𝔞])` with `𝔫` the
  annihilator of the kernel, `𝒪_D/𝔫 ≅ ℤ/N`. The condition `(−β + √D)/2 · Λ₂ ⊆ Λ₁`, together with `N Λ₂ ⊆ Λ₁`, says
  `𝔫 = (N, (−β + √D)/2)` kills the kernel; both ideals have norm `N`, so `𝔫` is the annihilator. GZ's formula holds
  for every `𝔫` and the leaf quantifies over every `β`, so the sign convention for `𝔫` does not matter.
* **`y_K`.** GZ define `y_K = Σ_{σ ∈ Gal(H/K)} φ(x)^σ`. By Shimura reciprocity (GZ II §1, Gross §1) `Gal(H/K)` permutes
  the Heegner points with a fixed `𝔫` simply transitively. So `y_K` is the sum of `φ` over a complete set of
  representatives, which is the leaf's form. This identification is a printed statement in both sources (UNVERIFIED
  locators).
* **`φ : X₀(N) → E` over `ℚ`.** `X₀(N)_ℚ` is not in Mathlib. A nonconstant morphism of smooth projective curves
  `X₀(N)_ℚ → E` is the same as a point of `E(ℚ(X₀(N)))` outside `E(ℚ)`. Here `ℚ(X₀(N))` is the field of
  `Γ₀(N)`-modular functions with rational `q`-expansion at `∞` (Shimura 1971, Ch. 6, the canonical model, and the
  `q`-expansion principle; Diamond–Shurman §7.5–7.7). That is gz-heegner's `IsRatModFnMero`. `φ(∞) = O` and `φ`
  nonconstant together say that `x∘φ` has a pole at the cusp `∞`.
* **`φ` at a point.** On `Y₀(N)(ℂ) = Γ₀(N)\ℍ` the morphism is `τ ↦ (X(τ), Y(τ))` where `X` is finite, and `O` where `X`
  has a pole. `modPt` reads this off from limits, so the junk values that `IsRatModFnMero` allows at poles play no
  role.

What cannot be stated today, and the smallest faithful replacement:

* `X₀(N)` as a scheme over `ℚ` (or as a coarse moduli space), its moduli interpretation over `ℚ`, and `J₀(N)`. These
  are replaced by the canonical-model function field `ℚ(X₀(N))` and the lattice model of `Y₀(N)(ℂ)`.
* Isogenies and endomorphism rings of elliptic curves as algebraic objects (Mathlib has neither for
  `WeierstrassCurve`). These are replaced by the lattice model `Hom(ℂ/Λ, ℂ/Λ') = {α : αΛ ⊆ Λ'}`.
* The Néron–Tate height on `J₀(N)(H)` and the Petersson norm, which enter Theorem I.6.3 itself. These are why the
  leaf is Ch. V's consequence for `E` (Tau Ceti's `canonicalHeight` on `E(K)`) with the constant forgotten.

**Rating: printed form (constant forgotten).** Gross–Zagier V.2.1 (with I.6.3 behind it) for every modular
parametrization, with Heegner points in their printed moduli definition. The departures from the print, each a
consequence of it, never stronger:

* the explicit constant `‖ω‖²/(c² u² √|D|)` is replaced by `∃ κ > 0`;
* `L(E/K, s)` is written as `L(f, s) L(f ⊗ χ_D, s)` (folded in, as in the old leaf);
* the moduli objects are rendered over `ℂ` in the lattice model, and `φ` through `ℚ(X₀(N))`. These are equivalent
  descriptions (standard theorems), not new content.

Possible reading risk (SPECULATIVE): whether V.2.1 is printed for an arbitrary modular parametrization or for the
strong Weil parametrization. For an arbitrary nonconstant `φ` with `φ(∞) = O` the `∃ κ > 0` form follows from the
optimal case: `φ` factors through `J₀(N) → E`, and `ĥ(λ(c)) = ĥ(λ(c_f))`, which is a positive multiple of `ĥ(c_f)`
because `λ` kills the other isotypic components. If a reader finds only the strong Weil case printed, the leaf should
be flagged pending reading, or restricted to `φ` of the form `weierPt E L (c φ_f)`. Our consumer only applies it to
that `φ`.

**Not vacuous** (`NonVacuous.lean`, compiled):

* complete sets of Heegner points exist (`exists_heegnerPointReps`);
* every `C_d`, `d ≡ 5 (mod 8)` squarefree, has an `IsModularParam` parametrization for every newform with
  `aₙ(f) = aₙ(C_d)` (`exists_modularParam_cd`, from gz-weil's proved `ShimuraCMParamCd`).

---

## 2. The proof (all VERIFIED, compiled; Lean names in `GrossZagierModuli.lean`)

Fix the data of `GrossZagierFormulaAt E`: `f`, `D`, `β`, a complete set `S` of Heegner forms of residue `β`, the period
lattice `L`, `c ∈ ℚ^×` with `c Λ_f ⊆ L`, `K`, `δ`, `ι`, `y` with `ι(y) = Σ_{Q ∈ S} weierPt E L (c φ_f(τ_Q))`, and `F`,
`G`. Apply the leaf to:

* `X = xPar = ℘_L(c φ_f) − b₂/12` and `Y = yPar`;
* `R = S`, `τ_Q = τ_Q`.

Three things must be checked.

**(a) `IsModularParam N E xPar yPar`** (`isModularParam_of`).

* `xPar, yPar ∈ ℚ(X₀(N))`: gz-heegner's `isRatModFnMero_coords` (proved from `paramRegular`, `paramCuspGrowth`,
  `paramQExpansion`).
* The Weierstrass equation: where `c φ_f(τ) ∉ L` it is `weierPt_some`. Where `c φ_f(τ) ∈ L`, `xPar` is not regular,
  by `not_tendsto_xPar`, so the condition is vacuous there.
* The pole at `∞` (`tendsto_norm_xPar`): `q² x(φ) = Ŷ(q)` with `Ŷ` analytic at `0` and `Ŷ(0) = c⁻² ≠ 0`
  (gz-heegner's `yF`), and `|q| = e^{−2π Im τ} → 0`.

**(b) `modPt` agrees with `weierPt E L (c φ_f)`** (`modPt_eq`).

* If `c φ_f(τ) ∉ L`, then `xPar` and `yPar` are analytic at `τ` (`paramRegular`). Their limits are their values, which
  form the point `weierPt`, and limits are unique.
* If `c φ_f(τ) ∈ L`, then `xPar` has no finite limit at `τ` (`not_tendsto_xPar`), so `modPt = O = weierPt`.
  - `1/(x∘φ − t)` is regular at `τ` with value `0` (`paramRegular`). It equals `1/(x∘φ − t)` at the points where
    `c φ_f ∉ L`, which accumulate at `τ`.
  - Why they accumulate (`frequently_zPar_notMem`): otherwise `c φ_f` would be locally constant or would take values
    in `L ∖ {c φ_f(τ)}` near `τ`. The second is impossible since `L` is discrete. In the first case `c φ_f` is
    constant on `ℍ` by the identity theorem, but `c φ_f(τ') ∉ L` for `Im τ'` large (gz-heegner's `exists_good_ball`).

**(c) `IsHeegnerPointReps N D β (Q ↦ τ_Q)`** (`isHeegnerPointReps_of`).

* *Each pair is a Heegner point* (`isHeegnerPair_of_form`).
  - `√D = 2Aτ + B` (`sD_eq_of_root`).
  - `End⟨1, σ⟩ = 𝒪_D` for a root `σ ∈ ℍ` of a form of squarefree discriminant `D` (`latEnd_span_root`; primitivity
    from squarefreeness, then `a ∣ y` by Bézout).
  - `⟨1/N, τ⟩ = (1/N)⟨1, Nτ⟩` with `Nτ` a root of `[A/N, B, CN]`.
  - The quotient is cyclic (`cyclic_pairOf`), and `(−β + √D)/2 = Aτ + (B − β)/2` with `2N ∣ B − β`.
* *No two are homothetic*: homothetic pairs come from `Γ₀(N)`-equivalent forms (gz-heegner's `equiv_of_pairHom`), and
  `S` has one form per class.
* *Every Heegner point is one of them* (`exists_rep`). This is the classification of Heegner points:
  1. **Adapted basis** (`normalize_pair`). From `Nv = aω₁ + bω₂` with `gcd(a, b, N) = 1` (exact order `N`), lift to a
     coprime pair `(a', b') ≡ (a, b) (mod N)` (`exists_coprime_lift`: add `N ∏ p` over the primes `p ∣ b` with
     `p ∤ a`). Complete it to `γ ∈ SL₂(ℤ)`; with `w = a'ω₁ + b'ω₂` and `τ = γ·(ω₂/ω₁) ∈ ℍ` we get
     `(Λ₁, Λ₂) = w·(⟨1, τ⟩, ⟨1/N, τ⟩)`.
  2. **The form** (`form_of_normalized`). Write `α₀ = (D + √D)/2 = m + nτ` and `α₀τ = p + qτ`. Then
     `α₀² = Dα₀ − (D² − D)/4` and the independence of `1, α₀` give `q = D − m` and `4np = 4qm − D² + D`. So `τ` is the
     root `τ_Q` of `Q = [n, 2m − D, −p]`, which has discriminant `D`, `n > 0` (imaginary parts) and is primitive
     (squarefree `D`). `α₀ ∈ End⟨1/N, τ⟩` gives `N ∣ n`. `(−β + √D)/(2N) ∈ ⟨1, τ⟩` gives `2N ∣ (2m − D) − β`.
  3. `S` contains a form `Γ₀(N)`-equivalent to `Q`. By gz-heegner's `pairHom_of_equiv` its pair is homothetic to
     `(Λ₁, Λ₂)`.

Then `Σ_{r ∈ S} modPt(τ_r) = Σ_{Q ∈ S} weierPt E L (c φ_f(τ_Q)) = ι(y)`, and the leaf gives the conclusion.

---

## 3. Deliverables

| File | Content | Check |
| --- | --- | --- |
| `ZInQKernel/Contrib/OneProof/GrossZagierModuli.lean` | objects, the leaf, §2–§4 proofs, `grossZagierFormulaCd_of_moduli` | `lake build` (VERIFIED) |
| `ZInQKernel/Contrib/OneProof/GrossZagierModuli/NonVacuous.lean` | `exists_heegnerPointReps`, `exists_modularParam_cd` | `lake build` (VERIFIED) |
| `scratch/gz-moduli/Target.lean` | verbatim copy of the target, `rfl` against the original | compiled (VERIFIED) |
| `scratch/gz-moduli/Check.lean` | `#print axioms` of the main theorems | standard axioms (VERIFIED) |
| `scratch/gz-moduli/Discharges.lean`, `discharges-output.txt` | `#discharges` | see §4 |
| `scratch/gz-moduli/MainEdit.lean` | `frozenTarget_gzmoduli`: `hL3` replaced by `X0ModuliGaloisMero`, `GrossZagierModuliCd`, `GrossConjugationCd` | standard axioms (VERIFIED) |
| `scratch/gz-moduli/autofold.json` | spec for the field `grossZagierFormulaCd` with the new leaf | JSON checked |

## 4. `#discharges`

`scratch/gz-moduli/discharges-output.txt` (VERIFIED, `lake env lean scratch/gz-moduli/Discharges.lean` after
`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.GrossZagierModuli`;
61 open hypotheses, 2950 theorems checked). At 60a3fac7 `GrossZagierFormulaCd` is not a bundle field: `hL3` is a
`frozenTarget` argument stated for all `E`. So the `C_d` theorem `grossZagierFormulaCd_of_moduli` is not listed, as
with gz-weil. To record the replacement against the current `frozenTarget`, the file also proves the all-`E` form
`grossZagierHeegner_of_moduli`: gz-heegner's `grossZagierHeegner_of_printed` with `GrossZagierModuli` in place of
`GZHL3.GrossZagierFormula`. `#discharges` lists it:

```
DISCHARGES [hL3] by ZInQ.GZModuli.grossZagierHeegner_of_moduli
  still assumes: [ZInQ.GZHL3.WeierstrassUniformization,
 ZInQ.GZHL3.StrongWeilCurve,
 ZInQ.GZHL3.IsogenyLattice,
 ZInQ.GZModuli.GrossZagierModuli,
 ZInQ.GZHL3.GrossConjugation,
 T5Glue.ShimuraMainCM,
 ZInQ.GZHeegner.X0ModuliGaloisMero]
  axioms: [propext, Classical.choice, Quot.sound]
```

For the `C_d` route, the integrator should first fold the `C_d` split of `hL3` (gz-weil's `MainEdit.lean`, or this
task's `MainEdit.lean`) with the field name `grossZagierFormulaCd`. After that, `autofold.json` applies.

## 5. What remains

* A reading of Gross–Zagier Ch. II §1, Ch. V §2 and Thm I.6.3 against the leaf's docstring. Locators and the explicit
  constant are UNVERIFIED. The question of an arbitrary versus the strong Weil parametrization is in §1.
* `X0ModuliGaloisMero` (gz-heegner) is the remaining non-printed hypothesis of the `hL3` chain.
* The explicit constant could be restored once a reading fixes the normalization of `ĥ` over `K`. Tau Ceti's
  `canonicalHeight` would then have to be compared with GZ's height.
