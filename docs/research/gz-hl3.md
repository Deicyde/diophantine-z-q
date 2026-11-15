# gz-hl3: `hL3 = GZDecomp.GrossZagierHeegner` split into the Gross–Zagier formula, Gross's conjugation relation and the Heegner point, over genuine definitions

Status: research note (task gz-hl3, 2026-11-15), branch `wip/gz-hl3` (base 24f97774, leaf-fold20).
Lean: `ZInQKernel/Contrib/OneProof/GrossZagierHeegner.lean` and
`ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Cd.lean` (new files; nothing else under `ZInQKernel/` was
edited). Development copy, discharge check and log: `scratch/gz-hl3/`.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published theorem with
an exact reference. **SPECULATIVE**: an assessment. This host has no network and no copy of Gross–Zagier, Gross
(1984), Shimura or Faltings, and `~/tyz-src/Period7.tex` is absent on this host this run. **Every theorem number,
locator and printed constant of the literature below is UNVERIFIED** (from memory).

---

## 0. Main result

**`hL3` is proved in Lean from six leaves stated over genuine definitions.** Two of them are textbook analysis
or arithmetic geometry and four are the Gross–Zagier/Gross/Shimura theory:

```lean
theorem ZInQ.GZHL3.grossZagierHeegner_of_leaves
    (hU : WeierstrassUniformization) (hSW : StrongWeilCurve) (hI : IsogenyLattice)
    (hHP : HeegnerPointRational) (hGZ : GrossZagierFormula) (hGC : GrossConjugation) :
    ZInQ.GZDecomp.GrossZagierHeegner
```

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` (VERIFIED, compiled with `lake build` and
`lake env lean`; `scratch/gz-hl3/Check.lean`, output `scratch/gz-hl3/out_check.txt`).

What is new compared with the composite `hL3`:

* **The Heegner point is a Lean object.** `heegnerC E L f c S = Σ_{Q ∈ S} weierPt E L (c · φ_f(τ_Q)) ∈ E(ℂ)`
  is built from:
  - Mathlib's Weierstrass `℘_L` and `℘'_L` (`PeriodPair`);
  - the Eichler integral `φ_f(τ) = Σ aₙ(f)/n · qⁿ` of the Tau Ceti newform;
  - the kernel's Heegner forms `[A, B, C]` (`N ∣ A`, `B² − 4AC = D`, from `TYZGenus/CM.lean`), with
    `B ≡ β (mod 2N)`;
  - a complete set `S` of `Γ₀(N)`-representatives.

  The parametrization is `ℚ`-rational because `c ∈ ℚ^×` and `c Λ_f ⊆ L`, where `L` is the period lattice of `E`
  (`g₂ = c₄/12`, `g₃ = c₆/216`).
* **The Gross–Zagier formula is stated for that point.** It says `L'(E/K, 1) = κ · ĥ(y_K)` with `κ > 0`, where
  `ĥ` is Tau Ceti's canonical height on `E(K)` and `L(E/K, s) = F(s) G(s)` is the product of the two entire
  continuations.
* **Gross's conjugation relation is stated for that point.** It says `σ y_K + ε y_K` is torsion, where `ε` is the
  root number pinned by Tau Ceti's functional equation (`rootNumber`).
* **The modular parametrization is separated into Eichler–Shimura (`StrongWeilCurve`) and Faltings
  (`IsogenyLattice`).** The rationality of the Heegner point is separated as `HeegnerPointRational`.
* **The glue is proved.** It covers:
  - the existence of a finite complete set of Heegner representatives (`heegnerRepsExist`, about 330 lines:
    reduction to Mathlib's fundamental domain of `SL₂(ℤ)`, the explicit transform of forms, and
    `[SL₂(ℤ) : Γ₀(N)] < ∞`);
  - `weierPt` lies on `E` (`weierPt_some`), so the definition is not junk;
  - the embedding `√D ↦ i√|D|`, and the fact that an automorphism of `ℚ(√D)` fixing `√D` is `1`;
  - `L'(E/K, 1) = F'(1) G(1) ≠ 0` at a simple zero;
  - `ĥ = 0` on torsion, the sign of a simple zero (the kernel's `signOfSimpleZero`) and `β² ≡ D (mod 4N)` (the
    kernel's Hensel lemma).

**Gross–Zagier's Chapter V consequences are proved from the leaves** (VERIFIED, compiled).
`heegnerPoint_infinite_iff` says that `y_K` has infinite order iff `L'(E/K, 1) ≠ 0`. `exists_rat_point_of_leaves`
says that if the analytic rank is 1 and there is a Heegner `D` with `L(E^D, 1) ≠ 0`, then `E(ℚ)` has a point of
infinite order.

**Verdict on the statements.** No leaf is stronger than its source as far as I can check without the papers (§4).
None is vacuous: the glue applies all of them at the instances `hL3` supplies. Three leaves are in printed form,
or printed form with a constant forgotten. Three are composites of textbook theorems (§1).

**The Cd form** (`GZStatements.GrossZagierHeegnerCd`) has the same split restricted to `C_d`. Only the
parametrization changes: Faltings is replaced by Shimura's theorem on CM curves (`ShimuraCMParamCd`). That removes
one deep theorem (Faltings). The four Heegner-point leaves stay the same theorems, applied to one family
(`grossZagierHeegnerCd_of_leaves`, compiled). So the Cd form makes the split slightly easier, not materially (§6).

---

## 1. The leaves

All in namespace `ZInQ.GZHL3`, file `Contrib/OneProof/GrossZagierHeegner.lean` §2. "Heegner setting" means the
hypotheses shared by the last three leaves:

- `E/ℚ` with `aₙ(E) = aₙ(f)` for a newform `f` of level `N` and trivial character;
- `D < −4` an odd fundamental discriminant with `HeegnerHyp N D`, and `β` with `4N ∣ D − β²`;
- `S` with `IsHeegnerReps N D β S`;
- `L` with `IsPeriodLattice E L`, and `c : ℚ`, `c ≠ 0`, with `PeriodsIn f c L`;
- `K` a quadratic number field with `δ² = D`, embedded by `ι` with `ι δ = i√|D|`;
- for the last two leaves, `y ∈ E(K)` with `ι(y) = heegnerC E L f c S`.

| Leaf | Statement (informal) | Source (UNVERIFIED locators) | Rating | Reason |
| --- | --- | --- | --- | --- |
| `WeierstrassUniformization` | `a³ − 27b² ≠ 0 ⇒ ∃ L, g₂(L) = a, g₃(L) = b` | Silverman, AEC, Thm VI.5.1; Serre, *Course in Arithmetic* VII §3 | **printed form** (textbook) | the printed statement verbatim over Mathlib's `PeriodPair.g₂/g₃` |
| `StrongWeilCurve` | `f` newform, weight 2, trivial character, rational `aₙ` ⇒ `∃ E'/ℚ` with `aₙ(E') = aₙ(f)` and `c Λ_f ⊆ L(E')`, `c ∈ ℚ^×` | Shimura 1971, Thm 7.14 and §7.5 (Eichler–Shimura); Manin 1972 (rational Manin constant) | **composite** (textbook) | the print constructs `E_f` as a quotient of `J₀(N)` and gives `L(E_f) = L(f)`; the analytic form (`Λ_f` up to a rational multiple is the period lattice of the invariant differential) adds the rationality of `φ^*ω` |
| `IsogenyLattice` | `L(E) = L(E')` ⇒ `m L' ⊆ L` with `m ∈ ℚ^×` | Faltings, Invent. Math. 73 (1983), Korollar 2; Silverman VI.4.1, III.5.3 | **composite** (research + textbook) | the print says "isogenous over `ℚ`"; Mathlib has no isogenies, so the isogeny is given by its analytic multiplier, which is rational because `α^*ω_E = m ω_{E'}` over `ℚ` |
| `HeegnerPointRational` | `Σ_{Q∈S} φ(τ_Q) ∈ ι(E(K))` | Gross 1984 §1–3; GZ 1986 II §1, V §1; Shimura 1971 Thm 5.4, §6.8 | **composite** (textbook) | the print says `y_K = Tr_{H/K} φ(x₁) ∈ E(K)` with `x₁ ∈ X₀(N)(H)`; here `X₀(N)` is replaced by its analytic uniformization, which requires Shimura reciprocity (Galois permutes the `h(D)` Heegner points of residue `β`) |
| `GrossZagierFormula` | `deriv (F·G) 1 = κ ĥ(y)`, `κ > 0` | GZ 1986, Thm I.6.3 and Ch. V Thm 2.1 | **printed form, constant forgotten** | the printed identity `L'(E/K, 1) = (explicit positive constant) · ĥ(y_K)`, with `∃ κ > 0` in place of the constant (a consequence); folded in: `L(E/K, s) = L(f, s) L(f ⊗ χ_D, s)` |
| `GrossConjugation` | `ε = 1 ⇒ σy + y` torsion; `ε = −1 ⇒ σy − y` torsion | Gross 1984 §5; GZ V §2 | **printed form** | the printed `ȳ_K = −ε y_K` mod torsion, for the same `y_K` |

The general leaves are the `…At E` forms quantified over every elliptic `E/ℚ`. `EichlerShimuraParamAt E` (there is
a `c ∈ ℚ^×` with `c Λ_f ⊆ L` for every `f` matching `E`) is proved from `WeierstrassUniformization`,
`StrongWeilCurve` and `IsogenyLattice` (`eichlerShimuraParamAt_of_leaves`).

**Why the constant is forgotten.** The printed constant involves the Petersson norm, or `‖ω‖²`, the Manin constant,
`u`, `h` and `√|D|`. The height normalization of the print (`ĥ` over `K` or `ℚ`, a factor 2) differs from Tau Ceti's
(the limit of the naive height of `x`, with Mathlib's number-field height). I cannot check these without the paper.
A wrong explicit constant would make the leaf false, while `∃ κ > 0` is implied by the print in every normalization.
The proof of `hL3` only needs `κ ≠ 0`. This is the same choice as the kernel's `TYZThm33`, which forgets the value
`2^{−1−ρ}𝓛(d)` of its coefficient.

---

## 2. The objects (all genuine)

| Lean | Meaning | Built from |
| --- | --- | --- |
| `eichler f τ` | `φ_f(τ) = Σ_{n≥1} aₙ(f)/n · e^{2πinτ} = 2πi ∫_{i∞}^τ f` | Tau Ceti `Newform`, `GZDecomp.coeff` (Mathlib `qExpansion`) |
| `PeriodsIn f c L` | `c(φ_f(γτ) − φ_f(τ)) ∈ L` for all `γ ∈ Γ₀(N)`, `τ ∈ ℍ`, i.e. `c Λ_f ⊆ L` | Mathlib `CongruenceSubgroup.Gamma0`, the `SL₂(ℤ)` action on `ℍ`, `PeriodPair.lattice` |
| `IsPeriodLattice E L` | `g₂(L) = c₄(E)/12`, `g₃(L) = c₆(E)/216` | Mathlib `PeriodPair.g₂/g₃`, `WeierstrassCurve.c₄/c₆` |
| `weierPt E L z` | `(℘_L(z) − b₂/12, (℘'_L(z) − a₁x − a₃)/2) ∈ E(ℂ)` (`O` on `L`) | Mathlib `weierstrassP`, `derivWeierstrassP`, `Affine.Point` |
| `HasResidue β Q`, `Gamma0Equiv`, `IsHeegnerReps N D β S` | `B ≡ β (mod 2N)`; `γ τ_Q = τ_{Q'}` with `γ ∈ Γ₀(N)`; one `Q ∈ S` in each class | kernel `TYZGenus.CM.HeegnerForm`, `tauH` |
| `heegnerC E L f c S` | `Σ_{Q∈S} φ(τ_Q)`, the image of `y_K` | the above |
| `y.canonicalHeight` | Néron–Tate height on `E(K)` | Tau Ceti `Affine.Point.canonicalHeight`, Mathlib `AdmissibleAbsValues` of a number field |
| `rootNumber f hχ`, `IsEntireCont`, `twistCoeff`, `HeegnerHyp`, `IsOddImagFundDisc` | as in gz-decomp | `GZDecomp` |

Checks of the definitions:

- **`IsPeriodLattice`** (VERIFIED, sympy): with `x = X − b₂/12` and `y = (Y − a₁x − a₃)/2`, the Weierstrass equation
  of `E` equals `(Y² − 4X³ + (c₄/12)X + c₆/216)/4`. So `z ↦ (℘(z), ℘'(z))` followed by this change of variables maps
  `ℂ/L` to `E(ℂ)` exactly when `g₂ = c₄/12` and `g₃ = c₆/216`, and `dx/(2y + a₁x + a₃) = dz`.
- **`weierPt`** (VERIFIED, compiled: `weierPt_some`): it lands on the curve for `z ∉ L`. The proof uses Mathlib's
  `derivWeierstrassP_sq` and `equation_iff_nonsingular`.
- **`eichler`** is a `tsum`. It converges, since `aₙ(f) = O(n)` for a cusp form of weight 2 (STANDARD, Hecke's
  bound). Otherwise it would be `0` and `GrossZagierFormula` would be false, not vacuous. Convergence is not proved
  in Lean; it is a property of the definition, not an assumption of any statement.

---

## 3. Glue proved in Lean (all VERIFIED, compiled)

| Lemma | Content |
| --- | --- |
| `heegnerRepsExist : HeegnerRepsExist` (`Reps.exists_reps`) | For `N ≥ 1` and any `D`, `β` there is a finite `S` with `IsHeegnerReps N D β S`. See the list below the table. |
| `Reps.transform`, `transform_tauH`, `residue_transform` | The form with root `γ • τ_Q` is `[Ad² − Bdc + Cc², −2Abd + B(ad + bc) − 2Cac, Ab² − Bab + Ca²]` (identities VERIFIED with sympy). It is primitive (via the inverse transform), positive (`4AA' = (2Ad − Bc)² − Dc²`), and has level `N` and residue `β` when `γ ∈ Γ₀(N)`. |
| `Reps.eq_cmPoint`, `cmPoint_root`, `tauH_injective`, `bounded_of_mem_fd` | `τ_Q` is the unique root of `Q` in `ℍ`; `τ_Q` determines `Q`; `τ_Q ∈ 𝒟 ⇒ A ≤ |D|` and `|B| ≤ |D|`. |
| `weierPt_some`, `disc_ne_zero`, `exists_isPeriodLattice` | `weierPt` is on `E`; `(c₄/12)³ − 27(c₆/216)² = Δ ≠ 0`, so uniformization applies. |
| `exists_embedding`, `algEquiv_eq_one_of_fix` | `ι : ℚ(√D) → ℂ` with `√D ↦ i√|D|`; `σ(√D) = √D ⇒ σ = 1`. |
| `deriv_ne_zero_of_order_one`, `deriv_mul_ne_zero` | `ord_{s=1} F = 1` and `G(1) ≠ 0` give `(FG)'(1) = F'(1)G(1) ≠ 0`. |
| `eichlerShimuraParamAt_of_leaves` | Compose: `c Λ_f ⊆ L(E_f)` and `m L(E_f) ⊆ L(E)` give `mc Λ_f ⊆ L(E)`. |
| `heegnerPoint_infinite_iff` | **GZ Ch. V consequence**: in the Heegner setting, `y_K` has infinite order iff `L'(E/K, 1) ≠ 0` (from `GrossZagierFormulaAt` and Tau Ceti's `canonicalHeight_eq_zero_iff_isOfFinAddOrder`, with Mathlib's Northcott property of number fields). |
| `exists_rat_point_of_leaves` | **GZ Ch. V rank consequence**: a simple zero of `L(E, s)` at `1` and a Heegner `D < −4` with `L(E^D, 1) ≠ 0` give a point of infinite order in `E(ℚ)`. |
| `heegner_at`, `grossZagierHeegner_of_leaves` | `hL3` for one curve, and for all curves. |
| `Cd.lean`: `grossZagierHeegnerCd_of_leaves`, `shimuraCMParamCd_of_leaves`, `…Cd_of` | The `C_d` form, and each restricted leaf implied by the general one. |

The steps of `heegnerRepsExist`:

- every `τ_Q` is moved into `𝒟` by `SL₂(ℤ)` (Mathlib `exists_smul_mem_fd`);
- the transformed form has `|A|, |B| ≤ |D|`, so there are finitely many of them;
- the decomposition `SL₂(ℤ) = ⋃ k Γ₀(N)` over finitely many `k` (Mathlib `instFiniteIndexGamma0`) gives a finite
  set `T` meeting every class;
- `S` is a choice of one element of `T` per class.

The proof of `hL3` (`heegner_at`), given the hypotheses of `hL3` at `E`:

1. Hensel gives `β`; `heegnerRepsExist` gives `S`; uniformization gives `L`; `EichlerShimuraParamAt E` gives `c`;
   `exists_embedding` gives `ι`.
2. `HeegnerPointRational` gives `y ∈ E(K)` with `ι(y) = heegnerC`.
3. `GrossZagierFormula` gives `(FG)'(1) = κ ĥ(y)`. The left side is nonzero, so `ĥ(y) ≠ 0`, so `y` is not torsion.
4. For `σ ∈ Aut(K/ℚ)`, either `σ(√D) = √D`, so `σ = 1` and `σy − y = 0`, or `σ(√D) = −√D`. In the second case
   `GrossConjugation`, with `ε = −1` from `signOfSimpleZero`, gives `σy − y` torsion.

The arbitrary `[Algebra ℚ K]` instance of `hL3` is identified with `DivisionRing.toRatAlgebra` (`Subsingleton`),
and `NumberField K` comes from `finrank = 2`.

---

## 4. Are the leaves true, and not stronger than the sources? (SPECULATIVE where not marked)

* **Why `c ∈ ℚ`, not `c ∈ ℝ` or `ℂ`.** A first draft had `c` real. For CM curves (`C_d`, CM by `ℤ[i]`), a complex
  `c` such as `c = i c₀` satisfies `c Λ_f ⊆ L` but gives the parametrization `[i] ∘ φ₀`, defined over `ℚ(i)` only.
  Then `Σ φ(τ_Q) = [i] y_K ∉ E(K)` when `y_K` has infinite order, and `HeegnerPointRational` would be **false**. A
  real `c` is safe (a homomorphism `ℂ/Λ_f → ℂ/L` commuting with complex conjugation is defined over `ℚ`), but the
  argument is delicate. The final statements take `c ∈ ℚ^×`. That is weaker for the three Heegner-point leaves (they
  quantify over fewer `c`), and the parametrization leaves still produce such a `c`: the Manin constant is rational,
  and a `ℚ`-isogeny has a rational multiplier, since `α^*ω_E = mω_{E'}` with both differentials over `ℚ`.
* **`HeegnerPointRational`.** For a `ℚ`-rational `φ` with `φ(∞) = O` (`weierPt 0 = O`), the set
  `{φ(τ_Q) : Q ∈ S}` is the `Gal(H/K)`-orbit of `φ(x₁)` (Gross 1984 §1–3, Shimura reciprocity), so the sum is in
  `E(ι(K))`. The subfield `ι(K) ⊂ ℂ` does not depend on the choice of `ι`; the normalization `ι(√D) = i√|D|` is kept
  only to match the print. Classes of Heegner points of residue `β` correspond to `Γ₀(N)`-classes of forms with
  `N ∣ A`, `B ≡ β (mod 2N)`, as in GZ II §1 (UNVERIFIED locator). The Lean proof checks that `Γ₀(N)` preserves this
  set (`residue_transform`).
* **`GrossZagierFormula`.** It holds for every `ℚ`-rational `φ`, of any degree (rescaling `φ` scales `ĥ(y_K)` and
  the printed constant together). `GZ`'s hypotheses on `(N, D)` are implied by the leaf's hypotheses
  (gz-statements §3.3: `D` odd, `≤ −7`, fundamental, `D ≡ β² (mod 4N)`, `(D, 2N) = 1`). `F G = L(E/K, s)` because
  `(D, N) = 1`. If `y` is torsion then `L'(E/K, 1) = 0` and every `κ` works.
* **`GrossConjugation`.** The sign convention is checked by the argument of Gross 1984 §5 as I recall it:
  `f | W_N = w f` with `ε = −w` in weight 2; `x̄_𝔞 = w_N(x_{𝔞'})`; `φ ∘ w_N = wφ + φ(w_N ∞)`, where `φ(w_N ∞)` is
  torsion (Manin–Drinfeld). So `ȳ_K = w y_K + tors = −ε y_K + tors`. Parity confirms both cases. For `ε = −1`,
  `y_K ∈ E(ℚ) ⊗ ℚ`, and BSD parity gives odd rank. For `ε = +1`, `y_K` lies in the minus part, i.e. `E^D(ℚ)`, and
  `ε(E^D) = ε χ_D(−N) = −1` (gz-statements: `jacobiSym_neg_level`). Independently, gz-statements' Kolyvagin
  cross-check covers the case actually used (`ε = −1`, `L(E^D, 1) ≠ 0`). `rootNumber` is by definition the sign of
  the proved functional equation (`Newform.frickeCompletedL_sub_eq`), so it is `ε`.
* **`StrongWeilCurve`, `IsogenyLattice`.** These hold by the arguments in their docstrings (Eichler–Shimura with a
  rational Manin constant; Faltings plus the analytic description of isogenies). The lattice `L` of a model is
  unique (it is determined by `g₂, g₃`), which is why both take `∀ L`.
* **`WeierstrassUniformization`** is the classical theorem.
* **Vacuity.** No leaf has unsatisfiable hypotheses on the instances used. `heegner_at` produces every hypothesis of
  the Heegner-point leaves from the hypotheses of `hL3`. These hold for `C_5` (gz-statements §3.3). `S`, `L`, `c` and
  `ι` exist by the glue and the two parametrization leaves.

---

## 5. Comparison with `h33 = TYZThm33` (TYZ Theorem 3.3, kernel `OneProof/TYZSplit.lean`)

Reused objects:

- the kernel's `TYZGenus.CM.HeegnerForm N D` (general `N`; `TYZThm33` uses `N = 32`), with `tauH` and `cmPoint`;
- the shared Tau Ceti `Newform`;
- `GZDecomp`'s `coeff`, `rootNumber` and `IsEntireCont`.

What could not be reused:

- `TYZThm33` lives on the eta-quotient model `X0.phiC : ℍ → A(ℂ)` of `X₀(32) = A` (32a1) and the pinned CM points
  `TYZ35.basePt n`. The Heegner points of `hL3` live on `X₀(32d²)` for `C_d`, and on `X₀(N)` for general `E`. The
  kernel has no model of `X₀(N)` for `N ≠ 32`. The analytic parametrization `weierPt E L (c φ_f(τ))` plays that
  role here for every `N`; for `N = 32`, `E = A`, `c = 1` it is the analytic description of `X0.phiC` that x0-32's
  leaves `X0.X0AnalyticModel` assert.
- **`TYZThm33` cannot supply `hL3`.** It is a Gross–Zagier formula for TYZ's genus points `P_χ ∈ A(H_n)`, but its
  encoding forgets the coefficient `2^{−1−ρ}𝓛(d)`. `Q d` is only constrained to be torsion when
  `ord_{s=1} L(E_d, s) > 1` (VERIFIED, read in `TYZSplit.lean`), so it never yields a point of infinite order.
  `GrossZagierFormula` keeps exactly the part that `TYZThm33` drops (`ĥ(y) ≠ 0` iff `L' ≠ 0`, through `κ > 0`).
- The two formulas have the same shape ("point = positive multiple of a central derivative"). Both are stated with
  the printed constant replaced by a positive or integral existential.

---

## 6. The Cd form (`GZStatements.GrossZagierHeegnerCd`)

`Cd.lean` (VERIFIED, compiled):

```lean
theorem ZInQ.GZHL3.grossZagierHeegnerCd_of_leaves (hU : WeierstrassUniformization)
    (hES : ShimuraCMParamCd) (hHP : HeegnerPointRationalCd) (hGZ : GrossZagierFormulaCd)
    (hGC : GrossConjugationCd) : ZInQ.GZStatements.GrossZagierHeegnerCd
```

The four `…Cd` leaves are the `…At (shortCurve (−d²))` forms for `d ≡ 5 (mod 8)` squarefree. Each is implied by the
general leaf (`shimuraCMParamCd_of_leaves`, `heegnerPointRationalCd_of`, `grossZagierFormulaCd_of`,
`grossConjugationCd_of`). The difference:

- **Parametrization.** For `C_d` it is Shimura's theorem on CM curves (Nagoya Math. J. 43 (1971): a CM elliptic
  curve over `ℚ` is a `ℚ`-quotient of `J₀(N)`), stated directly as `EichlerShimuraParamAt C_d`. This replaces
  `StrongWeilCurve` plus `IsogenyLattice`, so Faltings is not needed.
- **Gross–Zagier, Gross, Heegner rationality.** The same theorems, applied to one CM family at level `32 d²`. The
  human check shrinks to one level, but each leaf is still the full theorem.

**Assessment.** The Cd form makes the split slightly easier (one deep leaf fewer, and the reader checks only CM
curves). It does not reduce the Gross–Zagier part. Either form can be adopted: both compile, and the general split
implies the Cd split.

---

## 7. Integration

* **Contribution files.** `ZInQKernel/Contrib/OneProof/GrossZagierHeegner.lean` imports the module that defines the
  statement (`ZInQKernel.Contrib.GZDecomp.Decomp`), not `OneProof.Main`. The helper
  `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Cd.lean` also imports `GZStatements.Weak`.
* **`#discharges`** (VERIFIED, run 2026-11-15 after
  `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges`, 12982 jobs; full output in
  `scratch/gz-hl3/discharges-output.txt`):

  ```
  DISCHARGES [hL3] by ZInQ.GZHL3.grossZagierHeegner_of_leaves
    still assumes: [ZInQ.GZHL3.WeierstrassUniformization,
   ZInQ.GZHL3.StrongWeilCurve,
   ZInQ.GZHL3.IsogenyLattice,
   ZInQ.GZHL3.HeegnerPointRational,
   ZInQ.GZHL3.GrossZagierFormula,
   ZInQ.GZHL3.GrossConjugation]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 65 open hypotheses, 1311 theorems checked, 6 discharge one
  ```

  The other five discharging theorems in the count belong to contributions already in the tree.
* **The `Main.lean` edit** (`hL3` is a top-level hypothesis of `frozenTarget`, so autofold does not cover it):
  1. add `import ZInQKernel.Contrib.OneProof.GrossZagierHeegner`;
  2. in `ZInQ.OneProof.frozenTarget`, replace the binder `(hL3 : ZInQ.GZDecomp.GrossZagierHeegner)` by
     `(hU : ZInQ.GZHL3.WeierstrassUniformization) (hSW : ZInQ.GZHL3.StrongWeilCurve) (hI : ZInQ.GZHL3.IsogenyLattice)
     (hHP : ZInQ.GZHL3.HeegnerPointRational) (hGZ : ZInQ.GZHL3.GrossZagierFormula)
     (hGC : ZInQ.GZHL3.GrossConjugation)`;
  3. in the body, replace the last argument `hL3` by
     `(ZInQ.GZHL3.grossZagierHeegner_of_leaves hU hSW hI hHP hGZ hGC)`.

  The edited theorem compiles out of tree: `scratch/gz-hl3/MainEdit.lean` proves `ZInQ.FrozenTarget` from every
  other hypothesis of `frozenTarget` and the six leaves, with axioms `[propext, Classical.choice, Quot.sound]`
  (VERIFIED, `lake env lean`).
  `kinds.tsv` then gets six rows in place of `hL3`. `WeierstrassUniformization` is LEAF, textbook, printed form.
  `StrongWeilCurve`, `IsogenyLattice` and `HeegnerPointRational` are LEAF, composite, pending reading.
  `GrossZagierFormula` and `GrossConjugation` are LEAF, research, printed form (constant forgotten), unread. Each
  needs a `locators.md` row (§8).
* **Cd variant.** If the owner adopts `GrossZagierHeegnerCd`: use `grossZagierHeegnerCd_of_leaves` with the five Cd
  leaves, and replace `hL3` along with gz-statements' `frontier…grossZagierHeegnerCd` chain.

---

## 8. Pages a human must read (locators UNVERIFIED)

1. **GZ 1986 Ch. V, Thm 2.1 and (2.?) / Cor. (2.?).** The formula for `L'(E/K, 1)` in terms of `ĥ(y_K)`, with its
   positive constant. Check that `y_K = Tr_{H/K} φ(x₁)` for any modular parametrization `φ` defined over `ℚ`, and
   the hypotheses on `(N, D)`.
2. **GZ 1986 Thm I.6.3**, and the factorization `L(f, 1_K, s) = L(f, s) L(f ⊗ ε_D, s)`.
3. **Gross 1984 §5** (or GZ V §2). The relation `ȳ_K = −ε y_K` mod torsion, and the sign convention of `ε`.
4. **Gross 1984 §1–3 / GZ II §1.** Heegner points of residue `β` correspond to `Γ₀(N)`-classes of forms
   `[A, B, C]`, `N ∣ A`, `B ≡ β (mod 2N)`, and `Gal(H/K)` permutes them simply transitively.
5. **Shimura 1971 Thm 7.14** (and Manin 1972 for the rational Manin constant); **Faltings 1983 Korollar 2**;
   Silverman AEC VI.4.1, VI.5.1, III.5.3.
6. **Shimura, Nagoya Math. J. 43 (1971)** for the Cd variant.

---

## 9. Reproduction

```
lake build ZInQKernel.Contrib.OneProof.GrossZagierHeegner.Cd
lake env lean scratch/gz-hl3/Check.lean          # #print axioms, output scratch/gz-hl3/out_check.txt
lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges
lake env lean scratch/gz-hl3/Discharges.lean     # output scratch/gz-hl3/discharges-output.txt
```

`scratch/gz-hl3/HL3.lean` is the development copy of the main file (minus the header). `scratch/gz-hl3/Reps.lean`
is the development file of the representatives glue.

---

## 10. What remains, and the next step

* **Literature check.** Every locator and printed constant above is UNVERIFIED (§8).
* **`HeegnerPointRational` could be reduced further** to the kernel's `TYZGenus.Shimura.ShimuraReciprocityModFn`.
  That leaf is already derivable from `frozenTarget`'s open `T5Glue.ShimuraMainCM` and `T5Glue.X0ModuliGalois`.
  The reduction needs three more pieces, and this task did not attempt it.
  - **(a) A rationality leaf for the coordinates.** The coordinate functions of `φ` must lie in `ℚ(X₀(N))`. But
    `IsRatModFn` requires no poles on `ℍ`, and `x ∘ φ` has poles at `φ⁻¹(O) ∩ ℍ`. So either a variant of the
    reciprocity leaf allowing poles away from the Heegner points is needed, or rational functions of `(x∘φ, y∘φ)`
    regular at the `τ_Q`.
  - **(b) Glue for the ideal-class action on Heegner forms of level `N`.** For each `J`, `Q ↦ Q'` with
    `J·⟨1, τ_{Q'}⟩ = c⟨1, τ_Q⟩` and the same for `⟨1/N, τ⟩` must permute the classes of residue `β`.
  - **(c) Galois descent from `ℂ`-points fixed by `Aut(ℂ/K)` to `E(K)`.**

  Net effect: one composite leaf is replaced by a q-expansion-principle leaf, at the cost of a large amount of glue.
* **The printed constant** of the Gross–Zagier formula could be added as a second, explicit leaf once someone has
  read GZ V.2.1 and fixed the height normalization against Tau Ceti's `canonicalHeight`.
