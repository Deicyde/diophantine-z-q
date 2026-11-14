# leafq-check: the seven LEAF? candidates of leaf-fold4, checked

Task leafq-check, 2026-11-14. Base 67c2daf9 (fork main after w52). Lean: `scratch/leafq-check/` (results log
`log.md`). No file under `ZInQKernel/`, `blueprint/`, or another task's notes or scratch was edited. Model
work, no human review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source
(there is no network here; every theorem number below is UNVERIFIED unless it is marked otherwise).

## 1. Main result

**Two of the seven LEAF? candidates are no longer literature inputs** (VERIFIED, compiled, no `sorry`, axioms
`[propext, Classical.choice, Quot.sound]`):

1. **`GammaStarGen` is a theorem**: `gammaStarGen_proof : GammaStarGen`, proved from Mathlib alone
   (`scratch/leafq-check/GammaStarGen.lean`, `import Mathlib`, the Prop and its dependencies copied verbatim).
   The proof is a descent on the `Γ*`-orbit of `y = i + j` in the hyperboloid model. It replaces the
   cited route (Takeuchi's signature with Poincaré's polygon theorem and a covolume comparison) by a finite
   computation (§2.1).
2. **`ValenceBoundGammaStar` follows from the published valence formula alone**:
   `valenceBound_of_formula : ValenceFormulaGammaStar → ValenceBoundGammaStar`
   (`scratch/leafq-check/ValenceBound.lean`, `import Mathlib`). The new leaf `ValenceFormulaGammaStar` is
   the valence formula for `Γ*` (`Σ_{P∈T} ord_P F / e_P ≤ m/12`, with `e_P` defined in Lean as the order of
   the stabilizer in `Γ*/ℚ^×`). The stabilizer bound `e_P ≤ 6` is proved (`ellipticOrderLe6_proof`, by the
   crystallographic restriction), and so is the valence count `2 Σ ord_P ≤ m` (§2.2).

**Fold over leaf-fold4's chain** (`scratch/leafq-check/Fold.lean`, `import TailK`, the chain's own constants;
VERIFIED, 11 s):

```lean
theorem HDec.HSyn.sixContactMin_of_open5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeaves5) (g : OpenGlue4) : ZInQ.SixContactMin   -- 26 + 19 + 19 + 1 = 65 fields
theorem HDec.HSyn.sixContactMin_of_open6 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeaves6) (g : OpenGlue4) : ZInQ.SixContactMin   -- 65 fields, valence formula published form
```

`OpenAddedLeaves5` is leaf-fold4's `OpenAddedLeaves4` without `gammaStarGen`. `OpenAddedLeaves6` also
replaces `valenceBoundGammaStar` (LEAF?) by `ValenceFormulaGammaStar` (LEAF). The conclusion is the kernel's
`_root_.ZInQ.SixContactMin` (an `example` checks it). The count goes from 66 to 65 (LEAF? 7 → 5).

**The other five** (`CMDescends`, `ThetaRatiosAlgebraic`, `QMHauptmodul`, `X6ConicModel`, `Y3Connected`) are
true as stated. Each is a consequence of published results, but none is one printed theorem. None is
vacuous or stronger than its sources. Their splits into published parts are in §2.3-§2.7. Only
`CMDescends` could be split today into one published statement plus Lean glue (§2.3). The other four need
objects that are not in Mathlib (polarizations, canonical models, Shimura's uniformization).

### Verdict table

| candidate | published source(s) (numbers UNVERIFIED) | Lean statement vs. source | outcome |
|---|---|---|---|
| `GammaStarGen` | Takeuchi 1977 (`(2,4,6)` is arithmetic for disc 6); Poincaré's polygon theorem (Beardon §9.8) | consequence (composite) | **PROVED** from Mathlib: no longer a leaf (§2.1) |
| `ValenceBoundGammaStar` | valence formula for cocompact Fuchsian groups: Shimura 1971, Prop. 2.16 and Thm. 2.20; Rankin 1977, Thm. 4.1.4 (unitary multipliers); signature `(0;2,4,6)` (Takeuchi 1977; Elkies 1998 §3) | consequence (weaker: inequality, and `e_P ≤ 6`) | **REDUCED** to the leaf `ValenceFormulaGammaStar` (the published formula with the signature's value `m/12`); `e_P ≤ 6` and the count **PROVED** (§2.2) |
| `CMDescends` | Shimura–Taniyama 1961 (CM abelian varieties have models over number fields; Shimura 1998, §12.4 Prop. 26); with T11b (rigidity) and `A[3] ⊆ A(ℚ̄)` | consequence (composite) | split into one published statement plus glue (§2.3); glue not compiled |
| `ThetaRatiosAlgebraic` | `NS(A_ℚ̄) = NS(A_ℂ)` (algebraicity of polarizations); Thomae's formula (Mumford, *Tata Lectures on Theta II*, IIIa §8) or Shimura 1975/1976 (values of modular functions with algebraic Fourier coefficients); Igusa (one even theta-null vanishes exactly on products) | consequence (composite) | stays a leaf candidate: not splittable in Lean today (no polarizations) (§2.5) |
| `QMHauptmodul` | Lin–Yang 2020 Ex. 29 with (13)-(14); Igusa's theta expressions of `ψ₄`, `χ₁₀`; Hashimoto 1995 (modular embedding); signature of `Γ*` (rv-leaves-a §2.2) | consequence (composite) | stays a leaf candidate; its signature input is now partly a theorem (generation, `e_P ≤ 6`) (§2.4) |
| `X6ConicModel` | Kurihara 1979 (`X₀(6,1): x² + y² + 3 = 0`); Elkies 1998 §3 (`X*(6)`, coordinate `t`, `X₆ = X*(6)(√−t, √(3(t−1)))`) | consequence (composite; existential witness, stronger than the bundle `R1R2fp`, which it implies) | unchanged (§2.6) |
| `Y3Connected` | Deligne, PSPM 33 (1979) 2.1.3 and 2.6.3 (π₀ of Shimura varieties and the Galois action); Shimura 1970; with ts-hecke's orbit computation | consequence (existential witness; transferred to every R1fp triple by ts-hecke's `connectedSpace_of_R1fp`) | unchanged (§2.7) |

## 2. The candidates

### 2.1 `GammaStarGen`: proved

**Statement** (verbatim, period-glue): every `γ ∈ Γ* = ι(N_B(𝒪)⁺)` lies in the subgroup of `GL₂(ℝ)`
generated by `ι(x₄)`, `ι(x₆)` and the rational scalars, with `x₄ = 1 + i + j` and `x₆ = (j − 3)/2`.

**Published route (not used).** `Γ*/ℚ^×` is the `(2,4,6)` triangle group (Takeuchi 1977, UNVERIFIED). By
Poincaré's polygon theorem, `⟨g₄, g₆⟩` is a triangle group of covolume `π/6`, so it has index 1. This needs
the covolume of `Γ*` (Shimura's volume formula) and a geometric theorem.

**Proof in Lean** (`GammaStarGen.lean`, all numerics in `scratch/leafq-check/py/`, VERIFIED):
- `y = i + j ∈ 𝒪` and `y² = −1`. `y` is the pure quaternion of the fixed point `√2 + i` of `ι(x₄)`. For
  pure `v = bi + cj + dk` the bilinear form of `nrd` gives `pairY v = −2b + 3c`. On the hyperboloid
  `v² = −1`, `pairY v` is `cosh` of the hyperbolic distance between the fixed points of `v` and `y`.
- For `x ∈ N(𝒪)` with `nrd x > 0`, `v = x y x⁻¹` is a pure element of `𝒪` with `v² = −1`. `pairY v` is an
  integer (`pairY_int`), and `pairY v ≥ 1` because `pairY(x y x̄) − nrd x = 12((b−c)² + d²)` (`pairY_ge`).
- **Descent** (`descent`). Suppose `pairY v ≥ 2`. Conjugating by one of `x₆`, `x₆⁻¹`, `x₆x₄`, `(x₄x₆)⁻¹`
  lowers `pairY` by one of `b + 3d`, `b − 3d`, `−5b + 6c + 3d`, `−5b + 6c − 3d`. These are the Dirichlet
  walls of the four nearest orbit points, and the Dirichlet cone is compact, with vertices at the four
  order-6 points (`cosh = √3`). The certificate is
  `3·nrd(v) − (pairY v)² = (b+3d)(−5b+6c−3d) + (b−3d)(−5b+6c+3d)`. If no lowering were negative this
  would force `(pairY v)² ≤ 3`.
- **Base** (`P_base`). If `pairY v = 1` then `v = y` (`eq_yq`), so `x` commutes with `y` and
  `x = a + b y`. Then `u = x j x⁻¹ ∈ 𝒪` has `imJ = 1 + 4b²/N` and `imK = 2ab/N` (`N = a² + b²`).
  Integrality forces `(n₂ − 6)² + 4n₃² = 16`, so `ab = 0` or `a = ±b`, i.e. `x ∈ ℚ^×·{1, x₄, x₄², x₄⁻¹}`.
- Strong induction on `pairY` (`key`), and `gammaStarGen_proof`.

Checks: `lake env lean scratch/leafq-check/GammaStarGen.lean` gives 0 errors and standard axioms (about
90 s). Over the chain, `Fold.lean` proves the chain's own constant
`HDec.HSyn.G0Split.FibreQM.PeriodGlue.GammaStarGen` with the same proof.

**Consequence.** period-glue's `s8WeightExact_of hT gammaStarGen_proof` gives `S8WeightExact` from Igusa's
`ThetaModularity` (R4) alone. The field `gammaStarGen` leaves `OpenAddedLeaves4`
(`sixContactMin_of_open5`). The orientation question that period-glue §5.3 flagged for a human
(Poincaré's theorem) no longer arises.

### 2.2 `ValenceBoundGammaStar`: reduced to the published valence formula

**Statement** (verbatim, period-map). Let `F` be holomorphic on `ℍ`, not identically zero, with
`|F(γτ)| det(γ)^m = |cτ+d|^{2m}|F(τ)|` on `Γ*`. Then `2 Σ_{τ∈T} ord_τ F ≤ m` for every finite set `T` of
pairwise inequivalent points.

**Published statement.** Let `Γ` be a Fuchsian group of the first kind without cusps, and `F ≠ 0` an
automorphic form of weight `k` (unitary multiplier). Then
`Σ_{P∈Γ\ℍ} ord_P(F)/e_P = (k/2)(2g − 2 + Σ_j (1 − 1/e_j))` (Shimura 1971, Prop. 2.16 / Thm. 2.20; Rankin
1977, Thm. 4.1.4; UNVERIFIED). Here `e_P` is the order of the stabilizer of `P` in `Γ/(Γ ∩ ℝ^×)`.

**Is the Lean statement a consequence?** Yes. With the signature `(0;2,4,6)` (Takeuchi; Elkies §3) the right
side is `m/12`. Since `e_P ≤ 6`, `Σ_T ord_P ≤ 6·m/12`. The automorphy in absolute value gives a unitary
multiplier, since `F(γτ)/(j(γ,τ)^{2m}F(τ))·det(γ)^m` is holomorphic of modulus one off the zeros, hence
constant. Scalars `q ∈ ℚ^×` act trivially and satisfy the hypothesis. The Lean statement is weaker than the
published formula (inequality, and only `e_P ≤ 6`).

**Split** (`ValenceBound.lean`, VERIFIED):
- `ellOrder P := Nat.card {f : ℍ → ℍ // ∃ γ ∈ Γ*, γ • P = P ∧ f = (γ • ·)}`. This is Shimura's `e_P`: the
  image of `Γ*` in `PSL₂(ℝ)` acts faithfully, so distinct elements of the image are distinct maps.
- **LEAF `ValenceFormulaGammaStar`**: the published formula restricted to a finite set `T` of inequivalent
  points (all terms are `≥ 0`), in `ℝ≥0∞`, with right side `m/12` (the signature's value).
- **`EllipticOrderLe6`** (`0 < e_P ≤ 6`): **proved**, `ellipticOrderLe6_proof`, by the crystallographic
  restriction, without the signature. For `γ = ι(x)` fixing `P`, put `ζ = det γ/(cP+d)² = μ̄/μ`. Then
  `|ζ| = 1` and `2 Re ζ = 4 re(x)²/nrd(x) − 2`. The number `4 re(x)²/nrd(x)` is the trace of conjugation by
  `x` on the lattice `𝒪` (`adTrace_int`; identity checked in `py/vb_adtrace.py`), so it is an integer.
  Hence `ζ ∈ {±1, ±i, ±½ ± (√3/2)i}`. The map `γ ↦ ζ` is multiplicative on the stabilizer (`zeta_mul`) and
  determines the Möbius map (`zeta_inj`). A product `(±½ ± (√3/2)i)·(±i)` has real part `±√3/2`, so it is
  not among the eight. So the stabilizer embeds in `μ₄` or in `μ₆`.
- **The valence count** `valenceBound_of`: `Σ_T ord ≤ Σ_T 6·ord/e_P ≤ 6·m/12`. Also
  `valenceBound_of_formula`.

**For the human check** (period-glue §5.1): the normalization of `e_P` is now a Lean definition. The weight
convention `|cτ+d|^{2m}/det^m` is the published weight `k = 2m` for `γ/√det γ ∈ SL₂(ℝ)`. The covolume or
signature enters only through the constant `m/12`.

### 2.3 `CMDescends`

**Statement** (verbatim, period-map). Let `Q : QML3 ℂ` have CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`), i.e.
some `φ ∈ End_𝒪(Q.A)` with `φ² = −1` (resp. `φ² − φ + 1 = 0`, `φ² = −6`). Then there are `ιe : ℚ̄ → ℂ`,
`P : QML3 ℚ̄` with the same CM, and `Q'` with `IsBaseChangeOf ιe P Q'` and `Q.q ≅ Q'.q` as QM pairs (the
level structures need not match).

**Truth.** True. `φ` and `ι(i)` commute, with `ι(i)² = 2` and `φ² = −1`. So `End⁰(Q.A)` contains the
quartic CM field `ℚ(√2, i)` (resp. `ℚ(√2, √−3)`, `ℚ(√2, √−6)`), `2·dim A = 4`, and `Q.A` is of CM type.
No vacuity: CM points exist (`cm4_exists`, …, period-map).

**Published parts.**
1. **(ST) CM abelian varieties are defined over `ℚ̄`.** Every abelian variety over `ℂ` of CM type is
   isomorphic to `A₀ ×_{ℚ̄,ι} ℂ` for some abelian variety `A₀/ℚ̄` (Shimura–Taniyama 1961, §12.4; Shimura,
   *Abelian varieties with complex multiplication and modular functions*, 1998, Prop. 26; UNVERIFIED).
   The published statement is up to isomorphism (the model comes from the field of moduli or from
   spreading out a model over a finitely generated field and specializing, which CM rigidity allows). This
   answers period-glue §5.2's question "up to isomorphism, not isogeny": SPECULATIVE until checked
   against the printed statement.
2. **(T11b) rigidity**: `End(A₀) → End(A₀,ℂ)` is bijective. This is a textbook leaf already in the bundle
   (`T11b_Rigidity`). It descends `ι` and `φ`, and the descended maps are ring maps because `endBC` is a
   ring hom (period-map's `G0ModField.KernelField.endBC`).
3. **Torsion**: `A₀(ℚ̄)[3] → A₀(ℂ)[3]` is bijective (`bcPt` is injective; both have `3⁴` elements by T5
   `TorsionStructure`, a bundle leaf). It descends a level structure.

**Glue.** Build `Q'` as the base change of `P = (A₀, ι₀, η₀)` (`endBC`, `bcPt`, `dim_baseChange` exist in
the chain), and `QMIso Q.q Q'.q` from the isomorphism of (1). It was not compiled in this task (§3).
Recommended split: `CMDescends ⇐ ST_QM + T11b + TorsionStructure + glue`, with `ST_QM` the published (ST)
for an abelian surface over `ℂ` with `𝒪 ⊗ ℚ(φ) ⊆ End⁰`.

### 2.4 `QMHauptmodul`

**Statement** (verbatim, pkg-I1). There is a continuous `f : ℍ → P¹(ℂ)` equal to `jNum/jDen ∘ Ω` where
`jDen ≠ 0`, whose fibres are exactly the `Γ*`-orbits, surjective, with values `0, ∞, −16/27` at the fixed
points of `ι(x)` for `x ∈ 𝒪` with `x² = −1`, `x² − x + 1 = 0`, `x² = −6`.

**Verdict.** Composite, faithful (as rv-leaves-a §2.2 found). Its inputs:
1. Lin–Yang 2020 Ex. 29 (divisors of `ψ₄`, `χ₁₀` on the QM curve);
2. Igusa's theta expressions of `ψ₄`, `χ₁₀`;
3. the modular embedding `Ω` (Hashimoto 1995; a computation for this datum);
4. the signature of `Γ*`.

**What this task adds.** Input 4 enters at two places, and both are now theorems:
- "the CM points of each discriminant form one orbit": for `x² = −1` this is the descent of §2.1, which
  shows that every pure `v ∈ 𝒪` with `v² = −1` on the upper sheet is `Γ*`-conjugate to `y`;
- "`e_P ∈ {1, 2, 4, 6}`" (§2.2, the bound `e_P ≤ 6`).

**Analytic split** (not compiled; SPECULATIVE in size): `QMHauptmodul ⇐` R4 (`ThetaModularity`, leaf) +
`GammaStarGen` (proved) + the exact valence formula (the equality form of `ValenceFormulaGammaStar`) + the
value `−16/27` at the order-2 point (Lin–Yang / Elkies' coordinate: a genuine arithmetic input) + analytic
glue: meromorphy of `jNum/jDen ∘ Ω`, continuity into `OnePoint ℂ`, surjectivity by compactness of `Γ*\ℍ`.
- `Γ*`-invariance of `f` follows from R4 and the explicit `Sp₄(ℤ)` matrices (period-glue's `g8Auto_g4`,
  `g8Auto_g6`), now on all of `Γ*` by `GammaStarGen`.
- `j_θ(τ₄) = 0` follows from `det(CΩ + D)^{10} = −1` at the fixed point of `g₄`.
- The pole at `τ₃` and degree 1 follow from the exact valence formula: by the orders of `ψ₄`, `χ₁₀` at the
  elliptic points, `3a + 2b = 10` forces `ord_{τ₄} χ₁₀ = ord_{τ₃} χ₁₀ = 2`.

### 2.5 `ThetaRatiosAlgebraic`

**Statement** (verbatim, g0-thetapoint). Take `A` an abelian variety over a number field, `Φ : ℂ² → A(ℂ)_σ`
an analytic uniformization with kernel `Λ`, and any period matrix `Ω ∈ 𝔥₂` of `Λ`. Then some `θ_{m₀}(0,Ω)`
is nonzero, and every `θ_m(0,Ω)/θ_{m₀}(0,Ω)` is algebraic.

**Truth and vacuity.**
- True. If `dim A ≠ 2` the hypotheses cannot hold: a surjective holomorphic homomorphism `ℂ² → A(ℂ)` with
  discrete kernel forces `dim A = 2`. That case is vacuous, which is harmless; it is not a defect.
- `IsPeriodMatrix Λ Ω` ranges over all principal polarizations of `ℂ²/Λ` and all symplectic bases. Every
  Riemann form on `A(ℂ)` is algebraic (Appell–Humbert, Lefschetz; Mumford §3). Its class lies in
  `NS(A_ℚ̄) = NS(A_ℂ)`, so `(A_ℂ, L_Ω)` is defined over `ℚ̄`.

**Published parts.**
1. algebraicity and `ℚ̄`-rationality of polarizations (Mumford, *Abelian varieties*, §§1-3 and §23; NS of
   abelian varieties is invariant under extension of algebraically closed fields; STANDARD);
2. either
   - Shimura (Ann. of Math. 102 (1975), and Duke 43 (1976)): values of Siegel modular functions with
     algebraic Fourier coefficients at a point whose ppav is defined over `ℚ̄` are algebraic. The
     `θ_m/θ_{m₀}` are modular functions for `Γ(4,8)` with Fourier coefficients in `ℚ(ζ₈)`; or
   - in genus 2: Torelli (Weil 1957: a ppas over `ℚ̄` is `Jac(C)` or `E₁ × E₂`) with Thomae's formula
     (Mumford, *Tata II*, IIIa §8) and Jacobi's formula for products;
3. nonvanishing: in genus 2, an even theta-null vanishes only on products, and then exactly one does
   (Igusa 1962; Mumford, *Tata II*).

**Why not split in Lean.** Parts 1-3 need polarizations, the dual abelian variety or the moduli space
`A₂(4,8)`, none of which is in Mathlib. The candidate stays a LEAF? (composite).

### 2.6 `X6ConicModel`

**Statement** (verbatim, x6-kummer). Some witness `(Y, Φ, X, Ψ, fY, π₆)` of `R1R2fpFullProps` has a
Galois-equivariant bijection `X(ℚ̄) ≃ C(ℚ̄)` with `C : Y² + 3X² + 3Z² = 0`, under which
`π₆ = −16(X² + Z²)/(27Z²)`.

**Verdict.** Composite of:
- Kurihara 1979 (`X₀(6,1) : x² + y² + 3 = 0`, same quaternion class `(−1,−3) ≅ (−3,−3)` as `C`; VERIFIED by
  x6-kummer's Hilbert-symbol check);
- Elkies 1998 §3: `X*(6) = P¹_t` with `t = 0, 1, ∞` at discriminants `−24, −4, −3`, and the
  `(ℤ/2)²`-cover `X₆ = X*(6)(√−t, √(3(t−1)))`; the constants were re-derived independently by rv-h-cm §2.3.

It is an existential witness form, stronger than the bundle `R1R2fp` (which it implies; x6-kummer §3.6).
That is acceptable because the canonical model satisfies both and R1R2fp's witnesses are unique up to
isomorphism (ts-hecke `exists_surjective_of_R1fp`). Not splittable in Lean today: the comparison of
`π₆` with Elkies' `t` uses MobiusGlue and R2fp, already glue in the kernel, but the conic equation itself is
the published content. Unchanged.

### 2.7 `Y3Connected`

**Statement** (verbatim, ts-hecke): `∃ Y Φ, R1fpProps Y Φ ∧ ConnectedSpace Y.left`.

**Verdict.** Consequence of Deligne's description of `π₀` of Shimura varieties with the Galois action
(Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971) §§2-3; *Variétés de Shimura*, PSPM 33 (1979) 2.1.3,
2.6.3; Milne's notes §5, §13). For `G = B^×` and `K₃` this gives
`π₀(Y₃,ℚ̄) = ℤ̂^×/nrd(K₃) = (ℤ/3)^×`, with `Gal(ℚ̄/ℚ)` acting through the cyclotomic character, hence
transitively.
- The witness form is harmless: `connectedSpace_of_R1fp` transfers connectedness to every R1fp triple.
- The orbit computation (`scratch/ts-hecke/pi0_check.py`) lives in Shimura's analytic uniformization,
  which is not in Lean, so it cannot be compiled.

Unchanged.

## 3. What remains

- `CMDescends`: compile the glue of §2.3, i.e. `CMDescends` from `ST_QM`, `T11b_Rigidity` and
  `TorsionStructure` over the chain (`endBC`, `bcPt`, `dim_baseChange` are there).
- `QMHauptmodul`: the analytic split of §2.4 (large).
- Human checks: the published statements of (ST) (up to isomorphism), the valence formula's
  normalization (now explicit), Kurihara/Elkies' constants, Deligne's π₀.

## 4. Files

| file | content | check |
|---|---|---|
| `GammaStarGen.lean` | verbatim copy + proof | `lake env lean`, 0 errors, ~90 s |
| `ValenceBound.lean` | verbatim copy + `ValenceFormulaGammaStar`, `EllipticOrderLe6` (proved), `valenceBound_of(_formula)` | `lake env lean`, 0 errors, ~100 s |
| `QMHauptmodul.lean` | verbatim copy (PkgI1 §1-§6) | `lake env lean`, 0 errors |
| `CMDescends.lean`, `ThetaRatiosAlgebraic.lean`, `X6ConicModel.lean`, `Y3Connected.lean` | verbatim copy over the chain, `copy_iff` | `chk.sh`, 4-5 s each |
| `Fold.lean` | the proofs over the chain, `OpenAddedLeaves5/6`, `sixContactMin_of_open5/6` | `chk.sh`, 11 s |
| `chk.sh` | `lean` with leaf-fold4's compiled chain (copied outside the repository) and leaf-fold4's lake path | |
| `py/` | the computations (enumeration, Dirichlet cone, certificates, words, `Ad`-trace identity) | `~/pyenv/bin/python` |
