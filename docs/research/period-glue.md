# period-glue: period-map's six glue Props — two proved, four reduced

Task period-glue, 2026-11-13. Base 6f296292 (contains origin/wip/period-map). Lean:
`scratch/period-glue/` (results log `log.md`). No file under `ZInQKernel/`, `blueprint/` or another
task's directory was edited. Model work only, no human review.

## 1. Result

**Verdict.** None of the six statements was changed. As far as model review can tell, all six are
true and not vacuous. Every theorem below compiles with no `sorry` and only the axioms
`[propext, Classical.choice, Quot.sound]` (VERIFIED, §6).

| Prop (period-map) | outcome | Lean |
|---|---|---|
| `S8Nonzero` | **PROVED** from Mathlib alone: `Re Σθ_m⁸(Ω(√2+i)) < 0` | `S8.lean`: `s8Nonzero_proof` |
| `BaseChangeClassUnique` | **PROVED** from Mathlib alone (with mul-rigidity's proof of rigidity, copied) | `BCU.lean`: `baseChangeClassUnique_proof` |
| `S8WeightExact` | **REDUCED to two leaves, no glue left**: Igusa's `ThetaModularity` (pkg-I1, unchanged) and `GammaStarGen` (leaf candidate) | `W8.lean`: `s8WeightExact_of` |
| `QMTwistLattice` | REDUCED: `T11aRiemannHom` (textbook leaf) + `QMLatticeTwistAlg` (glue, pure algebra) | `QMTwist.lean`: `qmTwistLattice_of` |
| `PiTwistC` | REDUCED: R1fp, R2fp (existing leaves) + `TwistOrbitFinite`, `FibreTransferC` (glue) | `PiTwist.lean`: `piTwistC_of` |
| `SphereFactorAffine` | REDUCED: `HolP1OpenMap`, `HolP1FactorHol`, `SphereInjAffine` (glue, textbook complex analysis) | `SFA.lean`: `sphereFactorAffine_of` |

```lean
theorem s8Nonzero_proof : S8Nonzero
theorem baseChangeClassUnique_proof : PeriodMapH.BaseChangeClassUnique
theorem s8WeightExact_of (hT : PkgI1.ThetaModularity) (hG : GammaStarGen) : S8WeightExact
theorem qmTwistLattice_of (hH : T11aRiemannHom) (hA : QMLatticeTwistAlg) : QMTwistLattice
theorem piTwistC_of (Y Φ π) (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π)
    (hT : TwistOrbitFinite Y Φ) (hF : FibreTransferC Y π) : PiTwistC Y Φ π
theorem sphereFactorAffine_of (hA : HolP1OpenMap) (hB : HolP1FactorHol)
    (hC : SphereInjAffine) : SphereFactorAffine
```
(Namespace `HSyn.G0Split.FibreQM.PeriodGlue`.)

**Effect on period-map's targets.**
- `HauptmodulUnique ⇐ S8Nonzero, SphereFactorAffine`: now ⇐ the three complex-analysis glue Props.
- `QMDenZeroCM3 ⇐ S8Nonzero, S8WeightExact, ValenceBoundGammaStar`: now ⇐ `ThetaModularity`,
  `GammaStarGen`, `ValenceBoundGammaStar`. All three are leaves (one existing, two candidates for a
  human check, §4). There is no glue left in `QMDenZeroCM3`.
- `PeriodMapGlue` (own triple) ⇐ `BaseChangeClassUnique` (now proved), `PiTwistC`,
  `QMTwistLattice`, `CMDescends`: now ⇐ `TwistOrbitFinite`, `FibreTransferC`, `T11aRiemannHom`,
  `QMLatticeTwistAlg`, `CMDescends` (with R1fp, R2fp already hypotheses).

## 2. What was proved

### 2.1 `S8Nonzero` (certified theta evaluation, checked in Lean)

The certificate is structural. It needs only crude bounds on `q = e^{−π/2}`.
- **The point.** `Ω(√2+i) = Ω₀ = [[(−1+i)/2, 1], [1, −1+i]]` exactly (`omega_cm4`). So
  `Im Ω₀ = diag(1/2, 1)` and `(Ω₀)₀₁ = 1`.
- **Factorization** (`thetaConst_factor`). For each characteristic `m = (a, b)`,
  `θ_m(Ω₀) = u·Θ[a₁, b₁+a₂](τ₁)·Θ[a₂, b₂+a₁](τ₂)`. Here `τ₁ = (−1+i)/2`, `τ₂ = −1+i`,
  `Θ[a,b](τ) = Σ_n exp(πi(n+a/2)²τ + πi(n+a/2)b)` and `u = e^{−πi a₁a₂/2}`, so `u⁸ = 1`.
  The cross term `exp(2πi x₁x₂)` splits into characters, up to `exp(2πi n₁n₂) = 1`.
- **Phases.** Every term of `Θ[a,b](τ₂)` is one fixed eighth root of unity times a real number,
  so `Θ[a,b](τ₂)⁸ = ρ⁸ ≥ 0` (`th1_τ2`). Every term of `Θ[1,b](τ₁)` is `e^{πi(b/2−1/8)}` times a
  real number, so `Θ[1,b](τ₁)⁸ = −R⁸` (`th1_τ1_one`).
- **`Θ[0,b](τ₁) = P + σEi`, `σ = ±1`** (`re_th1_τ1_zero`):
  - the even terms are `e^{−πn²/2} > 0` and the odd terms are `−i(−1)^b e^{−πn²/2}`;
  - `P ≥ 1` (the term `n = 0`) and `E ≥ 2q` (`n = ±1`);
  - `P + E = Σ e^{−πn²/2} ≤ 1 + 2q/(1−q²)`, using the majorant `q⁻¹e^{−π|n|}`;
  - with `q ∈ [0.173, 0.2532]` (from `3 < π < 3.15` and `1 + x ≤ eˣ`):
    `1 ≤ P ≤ 1.0347` and `0.346 ≤ E ≤ 0.5411`;
  - then `Re (P + σEi)⁸ = p⁴ − 28p³u + 70p²u² − 28pu³ + u⁴ < 0` with `p = P²`, `u = E²`
    (`poly8_neg`).
- **Conclusion.** `Re θ_m(Ω₀)⁸ ≤ 0` for all 16 characteristics (`re_theta8_nonpos`), and `< 0`
  for `m = ((0,0),(0,1))` (`re_theta8_m0`). So `Re Σ_{m even} θ_m⁸(Ω₀) < 0`
  (`s8Omega0_re_neg`).
- **Numerics agree** (`py/s8_exact.py`, 60 digits, VERIFIED):
  - `θ_m(Ω₀)⁸/ϑ₀₀(i)¹⁶ ∈ {−1/4 (×4), −1 (×4), −4, 0}`;
  - `Σθ⁸(Ω₀) = −9 ϑ₀₀(i)¹⁶ = −33.907929576104924557…`, with `ϑ₀₀(i) = π^{1/4}/Γ(3/4)`.

### 2.2 `BaseChangeClassUnique`

- **The map.** The pullback property of `Q'` gives `θ : Q.A → Q'.A` over `Spec ℂ` with
  `θ ≫ g' = g` (`cmp`). Symmetrically it gives `θ'`.
- **Compatibilities.** Every compatibility is an equality of maps into the pullback `Q'.A`, checked
  after composing with `g'` (`eq_of_comp`): `θ'θ = 1`, `θθ' = 1`, equivariance, the level clause.
- **Identity section.** The level clause at `a = 0` sends the identity section to the identity
  section (`eta_comp`).
- **Rigidity.** Then rigidity makes `θ, θ'` homomorphisms: `isMonHom_of_geometricallyIntegral`,
  mul-rigidity's Mathlib proof, copied verbatim.
- **No new inputs.** period-map called rigidity "not in Mathlib". It is now proved, so this Prop
  needs nothing further.

### 2.3 `S8WeightExact`

- **Automorphy group** (`G8AutoSubgroup`). The elements of `GL₂(ℝ)⁺` with the exact automorphy of
  `G8` form a subgroup (cocycle of `denom`, `σ = id` on `GL₂⁺`). It contains every rational
  scalar (`g8Auto_scalar`).
- **Two generators.** `g₄ = ι(1+i+j)` (order 4, fixes `√2+i`) and `g₆ = ι((j−3)/2)` (order 6,
  fixes `i√3`). For each, with an explicit `M ∈ Sp₄(ℤ)`:
  - `M` is symplectic (`M4_symp`, `M6_symp`);
  - `Ω(gτ) = M·Ω(τ)` (`spAct_of_poly` with `I1_g4`, `I1_g6`);
  - `det g · det(CΩ(τ)+D)(τ−3)(τ+1) = −(cτ+d)²(gτ−3)(gτ+1)` (`spFactor_of_poly` with `I2_g4`,
    `I2_g6`);
  - with Igusa's `ThetaModularity` and `omegaSiegel_proof`, this gives automorphy for `g`
    (`g8Auto_gen`).
- **Where the matrices come from.**
  - `py/modemb.py` (sympy, exact) found `M`. Pick `y = xu` (`u ∈ 𝒪^×`) with `yμȳ = nrd(x)μ`;
    then `b ↦ y⁻¹bx` is symplectic for `Trd(μ⁻¹ab̄)`, and `M` is its block transpose.
  - The polynomial identities hold modulo `√2² = 2`. `py/w8_lean.py` printed the
    `linear_combination` coefficients.
- **The remaining input: generation.** `Γ* = ℚ^×·⟨g₄, g₆⟩` is `GammaStarGen` (§4.3).
  `py/triangle.py`: `x₂ = 2x₆x₄⁻¹ = (3/2)i + 2j + (1/2)ij` has `trd x₂ = 0`, so `g₆g₄⁻¹` has
  order 2.

## 3. The new named Props

| Prop | kind | statement (informal) | argument / source | size |
|---|---|---|---|---|
| `GammaStarGen` | **LEAF candidate** (flagged) | every `γ ∈ Γ*` is in the subgroup generated by `ι(1+i+j)`, `ι((j−3)/2)` and `ℚ^×` | signature `(0;2,4,6)` (Takeuchi 1977; Elkies 1998 §3) + Poincaré's polygon theorem + covolume; §4.3 | — |
| `T11aRiemannHom` | **LEAF** (textbook) | analytic representation of `Hom(A, A')` for uniformized `A, A'/ℂ`: `M` with `MΛ ⊆ Λ'` ↔ unique homomorphism | Mumford §1, Birkenhake–Lange Prop. 1.2.1, GAGA (UNVERIFIED locators); the kernel's `T11aRiemannEnd` is its case `A = A'` (`t11aRiemannEnd_of_hom`, proved) | — |
| `QMLatticeTwistAlg` | GLUE (pure algebra) | `∃ α ∈ Aut 𝒪, M ∈ GL₂(ℂ)` with `MΛ_τ = Λ_τ'`, `M ι(α a) = ι(a) M` ⇔ `τ' ∈ Γ*τ` | (⇐) `M = (cτ+d)⁻¹ι(u)`. (⇒) Skolem–Noether (kernel `TSkolemKW`), `Mι(u)⁻¹` central, `𝒪x = 𝒪u` | medium |
| `TwistOrbitFinite Y Φ` | GLUE (moduli) | on `ℚ̄`- and `ℂ`-points, the twist relation = orbits of a finite set `G ⊆ Aut(Y)` | R1hecke automorphisms; `rightMul` through `𝒪/3𝒪`; `Aut 𝒪/Inn` finite (mobius-glue); level structures over `K̄` differ by `(𝒪/3𝒪)^×`, the image of `𝒪^×` (strong approximation, or a finite check on 72 units) | medium |
| `FibreTransferC Y π` | GLUE (AG) | for `Y` proper smooth over `ℚ`: fibres of `π` = `G`-orbits on `ℚ̄`-points ⇒ on `ℂ`-points | `{π(p)=π(q)}` and `⋃ graph(g)` are closed in `Y×Y`; Jacobson; equal on closed points | medium |
| `HolP1OpenMap` | GLUE (textbook) | non-constant holomorphic `ℍ → P¹` is open | open mapping theorem in charts (Mathlib `AnalyticOnNhd.is_constant_or_isOpen`) + identity theorem | small-medium |
| `HolP1FactorHol` | GLUE (textbook) | `h = φ ∘ f`, `f` onto holomorphic, `φ` continuous ⇒ `φ` holomorphic on `P¹` | local inverse off critical values; removable singularity | medium |
| `SphereInjAffine` | GLUE (textbook) | injective holomorphic `φ : P¹ → P¹`, `φ(∞) = ∞` ⇒ affine | entire with pole at `∞` ⇒ polynomial; injective ⇒ degree 1 | medium |

**Checks on the new statements** (model checks):
- `FibreTransferC` carries the hypotheses `IsProper Y.hom` and `SmoothOfRelativeDimension 1 Y.hom`.
  Without them it is false: `Y = Spec ℂ` has no `ℚ̄`-points, so the hypothesis is empty while
  the conclusion fails.
- `T11aRiemannHom` is the published `Hom` statement; it is not stronger than it. Its `End` case is
  the kernel's `T11aRiemannEnd` verbatim.
- `GammaStarGen` is an equality of groups, and two inputs are needed to get it from the published
  signature:
  - the explicit triangle check: the hyperbolic distance between the fixed points of `g₄` and `g₆`
    has `cosh d = √3 = cot(π/4)cot(π/6)`, and `g₆g₄⁻¹` has order 2;
  - Poincaré's theorem.
- `SphereFactorAffine`'s pieces state holomorphy of `P¹`-valued maps by charts
  (`IsHolC1At`, `IsHolSphere`). These have the same shape as fibre-qm-period's `IsHolP1At`.

## 4. The two flagged leaves, restated, plus `GammaStarGen`

Locators are from memory (no network): UNVERIFIED. A human should check each one against the
printed source.

### 4.1 `ValenceBoundGammaStar` (period-map, unchanged)

The Lean statement:

> for `m : ℕ` and `F` holomorphic on `ℍ`, not identically zero, with
> `|F(γτ)| det(γ)^m = |cτ+d|^{2m}|F(τ)|` for all `γ ∈ Γ*`: for every finite set `T` of pairwise
> `Γ*`-inequivalent points, `2 Σ_{τ∈T} ord_τ F ≤ m`.

**Published statements it is a consequence of.**
1. **Valence formula** for a Fuchsian group `Γ` of the first kind, without cusps (cocompact).
   Let `F ≠ 0` be holomorphic of weight `k` with a unitary multiplier. Then
   `Σ_{P ∈ Γ\ℍ} ord_P(F)/e_P = (k/4π)·vol(Γ\ℍ) = (k/2)(2g − 2 + Σ_j (1 − 1/e_j))`.
   Here `e_P` is the order of the stabilizer of `P` in `Γ/{±1}`.
   - Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971),
     Theorem 2.20 together with Proposition 2.16 (degree of the divisor of an automorphic form);
     for weight `2m` with trivial multiplier.
   - Rankin, *Modular forms and functions* (1977), Theorem 4.1.4, for arbitrary unitary
     multiplier systems.
   - UNVERIFIED numbers.
2. **Signature** `(0; 2, 4, 6)` of `Γ*/ℚ^× = N_B(𝒪)⁺/ℚ^×`, `B` of discriminant 6. Sources:
   - Takeuchi, *Commensurability classes of arithmetic triangle groups*, J. Fac. Sci. Univ.
     Tokyo 24 (1977): the class II with `(2, 4, 6)` and quaternion algebra over `ℚ` ramified at
     `{2, 3}`;
   - Elkies, *Shimura curve computations*, ANTS-III (1998), §3: `X*(6)` and the `(2,4,6)` group;
   - Baba–Granath (2008), §3.1.
   - UNVERIFIED numbers.

**Derivation.**
- Weight `k = 2m`. The automorphy in absolute value makes `F(γτ)/(j(γ,τ)^k F(τ))` holomorphic of
  modulus one off the zeros, hence a unimodular constant: a unitary multiplier.
- The right side is `m(−2 + 1/2 + 3/4 + 5/6) = m/12`.
- Every `e_P ≤ 6`, so `Σ_{T} ord ≤ 6 · m/12 = m/2`.
- The inequality and `e_P ≤ 6` make the statement weaker than the published formula.

**What the human should check.**
- Shimura's normalization of `e_P` and of the weight, against period-map's `denom`, `det γ^m`.
- That the formula holds for `Γ*`, which contains elements of `det ≠ 1`: normalize by `√det` in
  `PSL₂(ℝ)`.

### 4.2 `CMDescends` (period-map, unchanged)

The Lean statement:

> a level-3 QM surface `Q/ℂ` with CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`) is, as a QM pair,
> isomorphic to the base change along some `ι : ℚ̄ → ℂ` of a level-3 QM surface `P/ℚ̄` with the
> same CM.

**Published statements.**
1. **CM abelian varieties are defined over `ℚ̄`.** An abelian variety over `ℂ` of CM type is
   isomorphic to the base change of one defined over a number field.
   - Shimura–Taniyama, *Complex multiplication of abelian varieties and its applications to
     number theory* (1961), §12.4, Proposition 26.
   - Shimura, *Abelian varieties with complex multiplication and modular functions* (1998),
     Proposition 26.
   - UNVERIFIED numbers.
   - It applies: `HasCM4` gives an endomorphism `φ` commuting with `ι(𝒪)`, `φ² = −1`. So
     `End⁰(A)` contains `B ⊗ ℚ(i)`, `A` is isogenous to `E²` with `E` CM, and `A` is of CM type.
2. **Endomorphisms are rigid.** For abelian varieties over an algebraically closed field `k` of
   characteristic 0 and `k ⊆ K`, `Hom_k(A,B) = Hom_K(A_K,B_K)`. This is the kernel's T11b
   (Mumford; Conrad, *Chow's K/k-image and K/k-trace*, Thm. 3.19; UNVERIFIED). It carries `ι`
   and the CM endomorphism down to `ℚ̄`.
3. **The level structure descends.** `A[3](ℚ̄) = A[3](ℂ)`, both of order `3⁴`.

**Derivation.** Take `A₀/ℚ̄` with `(A₀)_ℂ ≅ Q.A`. Transport `ι` and the CM endomorphism by (2), and
the level structure by (3). The composite iso gives `IsBaseChangeOf`.

**What the human should check.**
- The CM-type hypothesis in Shimura–Taniyama: `End⁰ ⊇` a CM field of degree `2 dim`.
- That (1) is stated for abelian varieties up to isomorphism, not up to isogeny.

### 4.3 `GammaStarGen` (new, LEAF candidate)

**Statement.** `∀ γ ∈ Γ*, γ ∈ ⟨ι(1+i+j), ι((j−3)/2), ℚ^×·1⟩`.

**Sources.** The signature of §4.1(2), and Poincaré's polygon theorem (Beardon, *The geometry of
discrete groups*, §9.8 and Thm. 10.6.x; UNVERIFIED).

**Derivation** (model argument; numerics VERIFIED in `py/triangle.py`).
- The fixed points `√2+i` and `i√3` of `g₄`, `g₆` are at hyperbolic distance `d` with
  `cosh d = 1 + (2 + (√3−1)²)/(2√3) = √3` (by hand).
- `√3 = cot(π/4)cot(π/6)`, the side of the triangle with angles `π/4, π/6, π/2`. Also
  `g₆g₄⁻¹ = ι(x₂)/2`, `trd x₂ = 0`, so it has order 2.
- So `⟨g₄, g₆⟩/±` is the `(2,4,6)` triangle group of that triangle, of covolume `π/6`. This
  equals the covolume of `Γ*/ℚ^×`, so the index is 1.
- A real multiple of a word in `x₄, x₆` that lies in `B` is a rational multiple, since `Z(B) = ℚ`.

**What the human should check.** The orientation (rotation senses) in Poincaré's theorem.

## 5. What remains

- **Glue, pure algebra.** `QMLatticeTwistAlg`. Skolem–Noether is in the kernel; the rest is
  `2×2` linear algebra over `ℚ(√2)`.
- **Glue, moduli and algebraic geometry.** `TwistOrbitFinite` and `FibreTransferC`.
- **Glue, complex analysis.** `HolP1OpenMap`, `HolP1FactorHol`, `SphereInjAffine`.
- **Leaves for a human check.** `ValenceBoundGammaStar`, `CMDescends`, `GammaStarGen` (§4), and the
  textbook `T11aRiemannHom`.
- **Inherited.** period-map's other inputs are unchanged (`R1bFamily` vs r1b-state, `CPtsTransport`,
  the SPECULATIVE premise bp-qmmoduli §2.2).

## 6. Lean outcomes (VERIFIED; outputs `scratch/period-glue/run_*.txt`)

| run | file | outcome |
|---|---|---|
| run_prereq | `lake build …QMLattice …JHeight …HeightConstant …Objects` | OK, 1m25s |
| run_base1 | `build_base.sh`: `PGBase.lean` = FibreQM 1-20634 + part_fqm + period-map's parts (= DevHeavy content), `lake env lean -o` | 0 errors, 3m13s |
| run_light_base | `build_light.sh`: `PGLight.lean` = period-map's PMLight.lean | 0 errors, 1m25s |
| run_bcu | `BCU.lean` (imports PGBase) | 0 errors; `baseChangeClassUnique_proof` standard axioms |
| run_qmtwist | `QMTwist.lean` (PGBase) | 0 errors; `qmTwistLattice_of` standard axioms |
| run_pitwist | `PiTwist.lean` (PGBase) | 0 errors; `piTwistC_of` standard axioms |
| run_s8 | `S8.lean` (PGLight) | 0 errors; `s8Nonzero_iff`, `s8Nonzero_proof` standard axioms |
| run_w8 | `W8.lean` (PGLight) | 0 errors; `s8WeightExact_of` standard axioms |
| run_sfa | `SFA.lean` (PGLight) | 0 errors; `sphereFactorAffine_of` standard axioms |

To reproduce, from the repository root:
1. the prereq build;
2. `scratch/period-glue/build_base.sh` and `scratch/period-glue/build_light.sh`;
3. `scratch/period-glue/check.sh scratch/period-glue/<File>.lean`.

The two base files are verbatim assemblies of fibre-qm-period's and period-map's committed files.
They are gitignored and rebuilt by the scripts.
