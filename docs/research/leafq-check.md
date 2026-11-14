# leafq-check: the seven LEAF? candidates of leaf-fold4, checked

Task leafq-check, 2026-11-14. Base 67c2daf9 (fork main after w52). Lean: `scratch/leafq-check/` (results log
`log.md`). No file under `ZInQKernel/`, `blueprint/`, or another task's notes or scratch was edited. Model
work, no human review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source
(there is no network here; every theorem number below is UNVERIFIED unless it is marked otherwise).

## 1. Main result

Of leaf-fold4's seven LEAF? fields, **one is now a theorem and three are replaced by smaller statements**.
Every proof below compiled with no `sorry`; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`
(VERIFIED).

| candidate | outcome | Lean |
|---|---|---|
| `GammaStarGen` | **PROVED** from Mathlib alone. It is a finite computation: a descent on the `Γ*`-orbit of `i + j` | `GammaStarGen.lean`: `gammaStarGen_proof` |
| `ValenceBoundGammaStar` | **REDUCED** to the published valence formula `ValenceFormulaGammaStar` (LEAF). The stabilizer bound `e_P ≤ 6` (crystallographic restriction) and the valence count are proved | `ValenceBound.lean`: `valenceBound_of_formula`, `ellipticOrderLe6_proof` |
| `CMDescends` | **REDUCED** to Shimura–Taniyama, `STQM` (LEAF), plus bundle leaves already present (`t11b`, `t5`, `r1r2`). The descent of `ι`, of the CM and of the level structure is proved; so is torsion descent from T5 | `CMDescendsGlue.lean`: `cmDescends_of`, `torsionDescends_of_t5` |
| `QMHauptmodul` | **NARROWED** to `QMHauptmodulBase3` (still LEAF?, composite): only the Hauptmodul property and the value `−16/27` remain | `QMHauptmodulCM.lean`: `qmHauptmodul_of_base2`, `base2_of_base3` |
| `ThetaRatiosAlgebraic`, `X6ConicModel`, `Y3Connected` | unchanged: true, each a consequence of published results, not splittable in Lean today | verbatim copies, §2.5-§2.7 |

Three of the `QMHauptmodul` clauses are now proved:
- the CM points of each discriminant `−4, −3, −24` form one `Γ*`-orbit;
- `j_θ(√2 + i) = 0`;
- `j_θ` has a pole at `i√3`, from R4, `GammaStarGen` and the valence bound.

What remains of it is the Hauptmodul property plus the value `−16/27` at the order-2 point.

**Fold over leaf-fold4's chain** (`scratch/leafq-check/Fold.lean`, `import TailK`, so the chain's own
constants; 22 s, VERIFIED):

```lean
theorem HDec.HSyn.sixContactMin_of_open10 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeaves10) (g : OpenGlue4) : ZInQ.SixContactMin
```

`OpenAddedLeaves10` (19 fields) is leaf-fold4's `OpenAddedLeaves4` (20 fields) with these changes:
- `gammaStarGen` deleted (proved);
- `valenceBoundGammaStar` → `valenceFormulaGammaStar`;
- `cmDescends` → `stQM`;
- `qmHauptmodul` → `qmHauptmodulBase3`.

An `example` checks that the conclusion is the kernel's `_root_.ZInQ.SixContactMin`. The intermediate forms
`sixContactMin_of_open5` … `open9` (one change at a time) compile as well.

| | research | textbook | added (LEAF / LEAF?) | glue | total |
|---|---|---|---|---|---|
| leaf-fold4 (`sixContactMin_of_open4`) | 26 | 19 | 20 (13 / 7) | 1 | 66 |
| **leafq-check (`sixContactMin_of_open10`)** | 26 | 19 | 19 (15 / 4) | 1 | **65** |

The four remaining LEAF? fields are `thetaRatiosAlgebraic`, `qmHauptmodulBase3`, `x6ConicModel` and
`y3Connected`. The new LEAFs are `valenceFormulaGammaStar` and `stQM`.

### Verdict table (published sources; numbers UNVERIFIED)

| candidate | published statement(s) | Lean statement vs. source | verdict |
|---|---|---|---|
| `GammaStarGen` | `Γ*/ℚ^×` is the `(2,4,6)` triangle group (Takeuchi, J. Fac. Sci. Univ. Tokyo 24 (1977)); Poincaré's polygon theorem (Beardon §9.8) | consequence (composite) | **theorem** (§2.1) |
| `ValenceBoundGammaStar` | valence formula for cocompact Fuchsian groups (Shimura 1971, Prop. 2.16 / Thm. 2.20; Rankin 1977, Thm. 4.1.4) with the signature `(0;2,4,6)` | consequence, weaker (inequality, `e_P ≤ 6`) | reduced to `ValenceFormulaGammaStar` = the published formula on finite sets, right side `m/12` (§2.2) |
| `CMDescends` | CM abelian varieties are defined over number fields (Shimura–Taniyama 1961 §12.4; Shimura 1998, §12.4 Prop. 26); rigidity of homomorphisms (T11b); `A[n]` is constant over `ℚ̄` (T5) | consequence (composite) | reduced to `STQM` (Shimura–Taniyama for QM surfaces with CM) + bundle leaves (§2.3) |
| `QMHauptmodul` | Lin–Yang 2020 Ex. 29 with (13)-(14); Igusa's theta expressions; Hashimoto 1995; signature of `Γ*`; Elkies 1998 §3 for the values | consequence (composite; rv-leaves-a §2.2) | narrowed to `QMHauptmodulBase3`; generation, `e_P ≤ 6`, orbit transitivity, `j_θ(√2+i) = 0` and the pole at `i√3` proved (§2.4) |
| `ThetaRatiosAlgebraic` | `NS(A_ℚ̄) = NS(A_ℂ)`; Shimura, Ann. Math. 102 (1975) / Duke 43 (1976), or genus-2 Torelli (Weil 1957) with Thomae (Mumford, *Tata II* IIIa §8); one even theta-null vanishes exactly on products (Igusa) | consequence (composite) | unchanged; vacuous only when `dim A ≠ 2`, which is harmless (§2.5) |
| `X6ConicModel` | Kurihara 1979 (`X₀(6,1): x² + y² + 3 = 0`); Elkies 1998 §3 (`X*(6)`, `t`, `X₆ = X*(6)(√−t, √(3(t−1)))`) | consequence (composite, existential witness; implies `R1R2fp`) | unchanged (§2.6) |
| `Y3Connected` | Deligne, PSPM 33 (1979) 2.1.3 and 2.6.3 (`π₀` of Shimura varieties, Galois action by reciprocity); Shimura 1970 | consequence (existential witness, transferred to every R1fp triple) | unchanged (§2.7) |

No candidate is false, vacuous or inert as stated.

## 2. The candidates

### 2.1 `GammaStarGen`: proved

**Statement** (verbatim, period-glue). Every `γ ∈ Γ* = ι(N_B(𝒪)⁺)` lies in the subgroup of `GL₂(ℝ)`
generated by `ι(1+i+j)`, `ι((j−3)/2)` and the rational scalars.

**Proof** (`GammaStarGen.lean`, `import Mathlib`, the Prop and its dependencies verbatim; numerics in
`py/gsg_*.py`, VERIFIED). Let `y = i + j ∈ 𝒪`, so `y² = −1`; `y` is the pure quaternion of the fixed point
`√2+i` of `ι(x₄)`.
- For `x ∈ N(𝒪)` with `nrd x > 0`, `v = xyx⁻¹` is a pure element of `𝒪` with `v² = −1`.
- `pairY v = −2b + 3c` (for `v = bi + cj + dk`) is `cosh` of the hyperbolic distance between the fixed
  points of `v` and `y`. It is an integer, and it is `≥ 1` because `pairY(x y x̄) − nrd x = 12((b−c)²+d²)`.
- **Descent.** If `pairY v ≥ 2`, conjugating by one of `x₆`, `x₆⁻¹`, `x₆x₄`, `(x₄x₆)⁻¹` lowers it. These
  are the Dirichlet walls `b ± 3d`, `−5b + 6c ± 3d` of the four nearest orbit points. Their cone is
  compact, with vertices at the order-6 points, `cosh = √3`. The certificate is
  `3·nrd v − (pairY v)² = (b+3d)(−5b+6c−3d) + (b−3d)(−5b+6c+3d)`.
- **Base.** `pairY v = 1` forces `v = y`. Then `x = a + by`, and the integrality of `x j x⁻¹` gives
  `(n₂−6)² + 4n₃² = 16`, so `x ∈ ℚ^×⟨x₄⟩`.

This replaces Takeuchi, Poincaré's theorem and the covolume comparison by a computation. The orientation
issue that period-glue §5.3 flagged no longer arises.

### 2.2 `ValenceBoundGammaStar`: reduced to the published valence formula

**Statement** (verbatim, period-map). Let `F` be holomorphic on `ℍ`, not identically zero, with
`|F(γτ)| det(γ)^m = |cτ+d|^{2m}|F(τ)|` on `Γ*`. Then `2 Σ_{τ∈T} ord_τ F ≤ m` for every finite set `T` of
inequivalent points.

**Published statement.** Let `Γ` be a Fuchsian group of the first kind without cusps and `F ≠ 0` an
automorphic form of weight `k` with unitary multiplier. Then
`Σ_{P∈Γ\ℍ} ord_P(F)/e_P = (k/2)(2g − 2 + Σ_j(1 − 1/e_j))`.

**Is the Lean statement a consequence?** Yes:
- for `Γ*` with signature `(0;2,4,6)` the right side is `m/12`;
- the multiplier is unitary, because the automorphy in absolute value makes
  `F(γτ)/(j^{2m}F(τ))·det^m` holomorphic of modulus 1, hence constant;
- `ord_P` is the order in the coordinate of `ℍ` (Shimura's `ν_P = ord_P/e_P`).

**Split** (`ValenceBound.lean`, `import Mathlib`, VERIFIED):
- `ellOrder P := Nat.card` of the Möbius maps of the stabilizer of `P` in `Γ*`. This is Shimura's `e_P`,
  since the image of `Γ*` in `PSL₂(ℝ)` acts faithfully.
- **LEAF `ValenceFormulaGammaStar`**: `Σ_{P∈T} ord_P F / e_P ≤ m/12` in `ℝ≥0∞`. It is the published formula
  dropped to a finite set of inequivalent points (all terms are `≥ 0`), with the signature's value `m/12`.
- **`EllipticOrderLe6` proved** (`ellipticOrderLe6_proof`), without the signature. For `γ = ι(x)` fixing
  `P`, `ζ = det γ/(cP+d)² = μ̄/μ` has `|ζ| = 1` and `2Re ζ = 4re(x)²/nrd(x) − 2`. The number
  `4re(x)²/nrd(x)` is the trace of conjugation by `x` on the lattice `𝒪` (`adTrace_int`), so it is an
  integer. Hence `ζ ∈ {±1, ±i, ±½ ± (√3/2)i}`. `γ ↦ ζ` is multiplicative and injective on Möbius maps,
  and `(±½ ± (√3/2)i)(±i)` is not among the eight values, so the stabilizer embeds in `μ₄` or in `μ₆`.
- **The valence count** `valenceBound_of`: `Σ_T ord ≤ 6·Σ_T ord/e_P ≤ m/2`.

The human check of period-glue §5.1 (the normalization of `e_P`) is now a Lean definition. The signature
enters only through the constant `m/12`.

### 2.3 `CMDescends`: reduced to Shimura–Taniyama

**Statement** (verbatim, period-map). Let `Q : QML3 ℂ` have CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`). Then
there are `ιe : ℚ̄ → ℂ`, `P : QML3 ℚ̄` with the same CM, and `Q'` with `IsBaseChangeOf ιe P Q'` and
`Q.q ≅ Q'.q`. True: `End⁰(Q.A) ⊇ ℚ(√2, φ)`, a quartic CM field, so `Q.A` is of CM type.

**New leaf `STQM`** (LEAF, a consequence of Shimura–Taniyama). A QM abelian surface over `ℂ` with CM by
`ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]` is isomorphic, as an abelian variety (homomorphisms both ways, inverse to each
other), to `A₀ ×_{ℚ̄,ιe} ℂ` for some `A₀/ℚ̄`. Published: an abelian variety over `ℂ` of CM type is
isomorphic to the base change of one over a number field (Shimura–Taniyama 1961 §12.4; Shimura 1998 §12.4,
Prop. 26; UNVERIFIED). It answers period-glue §5.2's question: the published statement is up to
isomorphism. This is SPECULATIVE until a human reads the printed statement.

**Glue, proved** (`CMDescendsGlue.lean`, over the chain, VERIFIED):
`cmDescends_of : STQM → T11b_Rigidity → TorsionDescends → R1R2fpRep → CMDescends`.
- `ι₀ = endBC⁻¹ ∘ conj_e ∘ ι`. T11b makes `endBC : End A₀ → End A₀,ℂ` bijective (`endBCe_bijective`).
- The CM endomorphism is carried by the same ring hom.
- The level structure is `η₀(a) = ι₀(a)·v₀`, where `v₀ ∈ A₀(ℚ̄)` is the descent of the 3-torsion point
  `e'(η(1))`.
- `Q'` comes from R1fp's naturality clause (the bundle's `r1r2`).
- `Q'.A ≅ A₀,ℂ` by the pullback property and period-glue's rigidity lemma
  `isMonHom_of_geometricallyIntegral`.
- `torsionDescends_of_t5 : TorsionStructure → TorsionDescends`: `A₀(ℚ̄)[n] → A₀,ℂ(ℂ)[n]` is injective,
  and both sets have `n^{2g}` elements by T5 (transported along `AlgebraicClosure k ≃ k`).

So `CMDescends` needs only `STQM` besides leaves already in the bundles (`t11b`, `t5`, `r1r2`).

### 2.4 `QMHauptmodul`: narrowed

**Statement** (verbatim, pkg-I1). There is a continuous `f : ℍ → P¹(ℂ)` with `f = jNum/jDen ∘ Ω` where
`jDen ≠ 0`. Its fibres are exactly the `Γ*`-orbits, it is surjective, and it takes the values
`0, ∞, −16/27` at the fixed points of `ι(x)` for every `x ∈ 𝒪` with `x² = −1`, `x² − x + 1 = 0`, `x² = −6`.

**Verdict.** Composite and faithful (rv-leaves-a §2.2). Its inputs are Lin–Yang's divisors, Igusa's theta
expressions, the modular embedding `Ω`, and the signature of `Γ*`.

**Proved here** (`QMHauptmodulCM.lean`, over the chain, VERIFIED):
- `orbit4`, `orbit3`, `orbit24`: every pure `w ∈ 𝒪` with `w² = −1` (resp. `−3`, `−6`) on the upper sheet
  is `g b g⁻¹` for a normalizer `g` with `nrd g > 0`, where `b = i+j` (resp. `j`, `2j+ij`). The descents
  are as in §2.1, using the Dirichlet walls of the nearest orbit points: 4 walls (disc −4), 6 walls
  (disc −3, max `cosh² = 3`), 4 walls (disc −24, max `cosh² = 2`). The certificates were found by
  `nlinarith`.
- `qmHauptmodul_of_base : QMHauptmodulBase → QMHauptmodul`, where `QMHauptmodulBase` asserts each CM
  clause only at `ι(i+j)`, `ι((1+j)/2)`, `ι(2j+ij)`. The proof transfers along orbits by the fibre clause,
  using `−γ` or `γ⁻¹` for the other sheet. This removes the docstring's claim "each such point is the
  unique elliptic point of `Γ*`" from the literature input.
- `base_of_base2 : QMHauptmodulBase2 → QMHauptmodulBase`, where `QMHauptmodulBase2` drops the disc −4
  clause. The value `0` at `√2 + i` follows from the formula clause:
  - `θ_{((1,1),(0,0))}(Ω(√2+i)) = 0`: `Ω₀` is a product matrix, and the odd one-variable `Θ[1,1]` vanishes
    (`th1_one_one`, with period-glue's `thetaConst_factor`, `omega_cm4`);
  - `Σθ⁸ ≠ 0` there (period-glue's `s8Omega0_proof`);
  - the fixed point of `ι(i+j)` is `√2 + i` (`fixed_by4`).

- `base2_of_base3 : ThetaModularity → GammaStarGen → ValenceBoundGammaStar → QMHauptmodulBase3 →
  QMHauptmodulBase2`, where `QMHauptmodulBase3` drops the disc −3 clause. **The pole at `i√3` is proved**:
  - `G20 = ∏θ²∘Ω/dF¹⁰` has exact weight-20 automorphy on all of `Γ*` (`LQ20.s20WeightExact_of`):
    period-glue's `G8` machinery with the second clause of R4, closed under `GammaStarGen`;
  - `ord_{i√3}(Σθ⁸∘Ω) ≥ 2` (period-map's `s8OrderCM3_of`);
  - the valence bound for `G20` at `{i√3, √2+i}`, with `G20(√2+i) = 0`, gives `ord_{i√3}(∏θ²∘Ω) ≤ 4`;
  - so `ord(jNum∘Ω) ≤ 8 < 10 ≤ ord(jDen∘Ω)`, the meromorphic order of `jNum/jDen` is negative, and `f`
    tends to `∞` (Mathlib's `tendsto_cobounded_of_meromorphicOrderAt_neg` and continuity of `f`);
  - `G20 ≢ 0` follows from the leaf's own surjectivity clause;
  - `i√3` and `√2+i` are inequivalent by `G8`'s automorphy.

  In the fold the three inputs are the bundle's `r4`, `gammaStarGen_proof` and
  `valenceBound_of_formula valenceFormulaGammaStar`.

**What `QMHauptmodulBase3` still asserts:**
- the Hauptmodul property: continuity, formula, fibres = orbits, surjectivity (Lin–Yang's degree-one
  divisor statement with Igusa and the modular embedding);
- the value `f = −16/27` at the order-2 point, which is genuine arithmetic content (Elkies' coordinate,
  Lin–Yang).

### 2.5 `ThetaRatiosAlgebraic`

**Statement** (verbatim, g0-thetapoint). Take `A` an abelian variety over a number field, a uniformization
`ℂ² → A(ℂ)_σ` with kernel `Λ`, and any period matrix `Ω ∈ 𝔥₂` of `Λ`. Then some `θ_{m₀}(0,Ω) ≠ 0`, and
every `θ_m/θ_{m₀}` is algebraic.

**Truth.**
- If `dim A ≠ 2` the hypotheses cannot hold (a discrete kernel of a surjective holomorphic homomorphism
  from `ℂ²`). That is harmless.
- Every Riemann form on `A(ℂ)` is algebraic, and its class lies in `NS(A_ℚ̄) = NS(A_ℂ)`.

**Published parts.**
1. algebraicity and `ℚ̄`-rationality of polarizations (Mumford, *Abelian varieties*, §§1-3, §23; STANDARD);
2. either
   - Shimura (Ann. of Math. 102 (1975); Duke 43 (1976)): values of modular functions with algebraic
     Fourier coefficients at `ℚ̄`-points of the moduli space are algebraic; the `θ_m/θ_{m₀}` are such
     functions for `Γ(4,8)`, with coefficients in `ℚ(ζ₈)`; or
   - in genus 2: Torelli (Weil 1957) with Thomae's formula (*Tata II*, IIIa §8) and Jacobi's formula;
3. nonvanishing: in genus 2 an even theta-null vanishes only on products, and then exactly one does.

**Why not split in Lean.** Polarizations, dual abelian varieties and `A₂(4,8)` are not in Mathlib.
Unchanged.

### 2.6 `X6ConicModel`

**Statement** (verbatim, x6-kummer). A witness of `R1R2fpFullProps` has a Galois-equivariant bijection
`X(ℚ̄) ≃ C(ℚ̄)`, `C : Y² + 3X² + 3Z² = 0`, with `π₆ = −16(X²+Z²)/(27Z²)`.

**Verdict.** Composite of:
- Kurihara 1979 (same quaternion class `(−1,−3) ≅ (−3,−3)`; VERIFIED by x6-kummer's Hilbert symbols);
- Elkies 1998 §3 (`X*(6)`, `t = 0, 1, ∞` at `−24, −4, −3`, the `(ℤ/2)²`-cover); the constants were
  re-derived independently by rv-h-cm §2.3.

The existential witness form is acceptable: the canonical model satisfies it, and R1fp witnesses are
related by surjections (ts-hecke). The conic equation is the published content. Unchanged.

### 2.7 `Y3Connected`

**Statement** (verbatim, ts-hecke): `∃ Y Φ, R1fpProps Y Φ ∧ ConnectedSpace Y.left`.

**Verdict.** A consequence of Deligne's `π₀` theorem with the reciprocity action:
- `π₀(Y₃,ℚ̄) = ℤ̂^×/nrd(K₃) = (ℤ/3)^×`, with `Gal(ℚ̄/ℚ)` acting through the cyclotomic character;
- ts-hecke's orbit computation, which lives in Shimura's analytic uniformization (not in Lean).

`connectedSpace_of_R1fp` makes the witness form harmless. It is not derivable from the bundle's
`R1pi0Props` (`X₆` geometrically connected), which says nothing about level structures. Unchanged.

## 3. What remains

- **LEAF?**: `thetaRatiosAlgebraic`, `qmHauptmodulBase3`, `x6ConicModel`, `y3Connected`.
- **New LEAFs for a human check** (both up to the published statement's exact form):
  - `valenceFormulaGammaStar`: Shimura's normalization, and the signature's constant `m/12`;
  - `stQM`: up to isomorphism, as stated.
- **Integration**: append `Fold.lean`'s body to leaf-fold4's chain (after `TailK`). It uses only chain
  constants, Mathlib and the kernel imports of `TailK`.

## 4. Files (`scratch/leafq-check/`)

| file | content | check (VERIFIED) |
|---|---|---|
| `GammaStarGen.lean` | verbatim copy + `gammaStarGen_proof` | `lake env lean`, 0 errors, ~90 s |
| `ValenceBound.lean` | verbatim copy + `ValenceFormulaGammaStar`, `ellipticOrderLe6_proof`, `valenceBound_of_formula` | `lake env lean`, 0 errors, ~100 s |
| `QMHauptmodul.lean` | verbatim copy (PkgI1 §1-§6) | `lake env lean`, 0 errors |
| `QMHauptmodulCM.lean` | orbits, weight-20 automorphy, `QMHauptmodulBase(2,3)`, `qmHauptmodul_of_base2`, `base2_of_base3` | `chk.sh`, 19 s |
| `CMDescends.lean`, `ThetaRatiosAlgebraic.lean`, `X6ConicModel.lean`, `Y3Connected.lean` | verbatim copies over the chain, `copy_iff : copy ↔ chain Prop := Iff.rfl` | `chk.sh`, 4-5 s |
| `CMDescendsGlue.lean` | `STQM`, `TorsionDescends`, `torsionDescends_of_t5`, `cmDescends_of` | `chk.sh`, 8 s |
| `Fold.lean` | all proofs over the chain, `OpenAddedLeaves5`-`10`, `sixContactMin_of_open5`-`10` | `chk.sh`, 22 s |
| `chk.sh` | `lean` with leaf-fold4's compiled chain (copied to `~/lqc-olean`, outside the repository) and leaf-fold4's lake `LEAN_PATH` | |
| `py/` | enumeration, Dirichlet cones, certificates, words, normalizer witnesses, the `Ad`-trace identity | `~/pyenv/bin/python` |

`chk.sh` needs leaf-fold4's compiled olean chain (`scratch/leaf-fold4/chain.sh`). Without it, append the
body of a chain file to `scratch/leaf-fold4/Leaves4.lean` and compile the flat file (about 18 minutes).
