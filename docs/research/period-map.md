# period-map: `PeriodMapGlue`, `HauptmodulUnique` and `QMDenZeroCM3` reduced to smaller named Props

Task period-map, 2026-11-13. Base 322303a2. Lean: `scratch/period-map/` (results log `log.md`).
The three targets are fibre-qm-period's glue under `FibreQMPeriod`
(`scratch/fibre-qm-period/part_fqm.lean`, `docs/research/fibre-qm-period.md`). No file under
`ZInQKernel/`, `blueprint/` or another task's directory was edited. Model work only, no human
review.

## 1. Result

**Verdict.** As far as model review can tell, all three statements are true and not vacuous. None
was changed. Each is proved in Lean, with no `sorry` and only the axioms
`[propext, Classical.choice, Quot.sound]` (VERIFIED, §6), from strictly smaller named Props, each a
`def … : Prop` with a docstring giving its step, its source and the argument. The final forms:

```lean
theorem PeriodMap.hauptmodulUnique_of' (hS : S8Nonzero) (hSF : SphereFactorAffine) :
    HauptmodulUnique
theorem PeriodMap.qmDenZeroCM3_of'' (hS : S8Nonzero) (hW : S8WeightExact)
    (hV : ValenceBoundGammaStar) : QMDenZeroCM3
theorem PeriodMapH.periodMapGlue_of (Y Φ π) (h1 : R1fpProps Y Φ) (hBC : BaseChangeClassUnique)
    (hPT : PiTwistC Y Φ π) (hTL : QMTwistLattice) (hCM : PiCMC Y Φ π) (hCF : CMFixedHasCM) :
    PeriodMapGlue Y Φ π
theorem PeriodMapH.cmFixedHasCM_of (hR : T11aRiemannEnd) : CMFixedHasCM
```

`periodMapGlue_of` uses only the naturality clause of `R1fpProps`. At the leaf's own triple
(`periodMapGlue_own`) the bundle `R1R2fp` supplies that clause, and T11a is already a hypothesis of
fibre-qm-period's theorem, so `PeriodMapGlue` needs four glue Props. (Namespaces:
`HSyn.G0Split.FibreQM.PeriodMap` and `HSyn.G0Split.FibreQM.PeriodMapH`.)

**End to end** (`fibreQMPeriod_periodMap`, compiled). This is fibre-qm-period's
`fibreQMPeriod_main` with the three targets replaced by their pieces:

```lean
theorem fibreQMPeriod_periodMap (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hCN : QMClassNumberOne) (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h))
    (hBC : BaseChangeClassUnique) (hPT : PiTwistC (ownY h) (ownΦ h) (ownπ h))
    (hTL : QMTwistLattice) (hD : CMDescends)
    (hS : S8Nonzero) (hSF : SphereFactorAffine) (hW : S8WeightExact)
    (hV : ValenceBoundGammaStar) (hCP : CPtsTransport) : ThetaPt.FibreQMPeriod
```

**Proved here, in Lean.**
- **`Ω(τ)` lies in Siegel space, and the theta constants are holomorphic along it.**
  - `omegaSiegel_proof`: for `τ ∈ ℍ`, `Ω(τ)` is symmetric with positive definite imaginary part.
    The proof uses a closed form, `Ω = adj(F₀P⁻¹)E/det(F₀P⁻¹)` with
    `det = −√2(τ−3)(τ+1)/2`. With `τ = x+iy`: `Im Ω₀₀ = (y/2)Q/|d|²` and `Im Ω₁₁ = 2 Im Ω₀₀`, where
    `Q = (4−√2)(x²+y²) − 6√2x + 12 + 3√2 > 0`; and `det Im Ω = 12y²/(|τ−3|²|τ+1|²)`. Every
    `linear_combination` coefficient comes from `py/omega_lean.py`.
  - `thetaOmegaAnalytic_proof`: hence `Σθ⁸∘Ω` and `∏θ²∘Ω` are analytic on `ℍ`. The entries of
    `Ω` are holomorphic. Near `τ₀`, `wᵀ Im Ω(τ) w ≥ c|w|²` uniformly, from the identity
    `(p+r)Q(w) − (pr−q²)|w|² = (pw₀+qw₁)² + (qw₀+rw₁)²` and continuity. Each theta term is then
    bounded by a summable Gaussian (Mathlib's Jacobi-theta bound), and
    `differentiableOn_tsum_of_summable_norm` applies.
- **`QMHauptmodul`'s `f` is holomorphic into `P¹(ℂ)`** at every point (`isHolP1At_of_hauptFn`).
  The proof uses the identity theorem and removable singularities.
- **The three CM points exist** (`cm4_exists`, `cm3_exists`, `cm24_exists`). The elements are
  `x = i+j`, `(1+j)/2`, `2j+ij`, with fixed points `√2+i`, `i√3`, `i√(9+6√2)`.
- **The Möbius step.** An affine `A` with `h = A∘f` fixes `0` and `−16/27`, so `A = id`.
- **`ι` and `𝒪`.** `ι` is multiplicative (`iota_mul`). `𝒪` is closed under products
  (`inO_mul`). `Γ*` is closed under inverses (`gammaStar_inv`) and contains `ι((1+j)/2)`.
- **The valence argument** for `QMDenZeroCM3`:
  - a point `Γ*`-equivalent to `i√3` is fixed by some `ι(x')` with `x'² − x' + 1 = 0`
    (`cm3_of_equiv`);
  - the counting itself.
- **From the exact automorphy `S8WeightExact`:**
  - the absolute-value form (`s8Weight8_of`);
  - the double zero at `i√3` (`s8OrderCM3_of`). The fixed point gives `G8(τ₃) = w⁸G8(τ₃)` with
    `w = cτ₃+d = e^{iπ/3}`, `w⁸ ≠ 1`. Differentiating the functional equation gives
    `G8'(τ₃)(1 − w¹⁰) = 0` with `w¹⁰ = −w`. The order is then read off
    `analyticOrderAt_eq_natCast`.
- **`CMFixedHasCM` from T11a** (`cmFixedHasCM_of`):
  - at a fixed point of `ι(x)`, `λ = cτ+d` is the eigenvalue of `ι(x)` on `(τ,1)ᵀ`;
  - `z ↦ λz` preserves `Λ_τ`, since `λι(b_k)(τ,1)ᵀ = ρ(ι(b_k x))(τ,1)ᵀ` with fibre-qm-period's
    analytic representation `ρ`;
  - it lifts to some `φ ∈ End(A)` (T11a);
  - `ρ` is injective by T11a's uniqueness, so `φ` commutes with `ι(𝒪)` and satisfies the equation
    of `x`.
- **`PiCMC` from `CMDescends`** (`piCMC_of`). A CM object over `ℂ` is, as a QM pair, the base
  change of a CM object `P/ℚ̄`. Take the `ℚ̄`-point of `P` (`Φ` is a bijection). R2fp's CM clause
  gives its `π`-value; R1fp naturality, `BaseChangeClassUnique` and `ToP1.val_comp` carry it to
  `ℂ`; `PiTwistC` (⇐, trivial twist) carries it to the given point.
- **The plumbing of `periodMapGlue_of`.** R1fp naturality gives the base change,
  `ToP1.val_comp` moves `π` along it, and `1 ∈ Γ*`.

## 2. The named Props

Sizes are SPECULATIVE.

| Prop | kind | statement (informal) | source / argument | size |
|---|---|---|---|---|
| `ValenceBoundGammaStar` | **LEAF** (consequence of published) | if `F` is holomorphic on `ℍ`, not identically zero, and `\|F(γτ)\| det γ^m = \|cτ+d\|^{2m}\|F(τ)\|` on `Γ*`, then `2 Σ_{τ∈T} ord_τ F ≤ m` for every finite set `T` of pairwise `Γ*`-inequivalent points | valence formula `Σ ord_P/e_P = (k/2)(2g−2+Σ(1−1/e_j))` for Fuchsian groups of the first kind (Shimura 1971 §2.4; Rankin 1977 Thm 4.1.4, unitary multipliers; UNVERIFIED locators), plus the signature `(0;2,4,6)` of `Γ*/ℚ^×` (Elkies 1998 §3; Baba–Granath §3.1; UNVERIFIED). The total is `m/12`, and `e_P ≤ 6` | — |
| `S8Nonzero` | GLUE (numerical) | `Σθ_m⁸(Ω(√2+i)) ≠ 0` | value `−33.9079295761…` (VERIFIED numerically). A Lean proof needs certified bounds for theta series at an algebraic point | small-medium |
| `S8WeightExact` | GLUE | `G8(γτ)·det γ⁴ = (cτ+d)⁸ G8(τ)` on `Γ*`, with `G8 = Σθ⁸∘Ω/((τ−3)(τ+1))⁴` (trivial multiplier) | `Ω(γτ) = M_γ·Ω(τ)` with `M_γ ∈ Sp₄(ℤ)`, and Igusa's `ThetaModularity` (pkg-I1 leaf). VERIFIED numerically: multiplier `1` to 9-40 digits for 7 elements, among them the elliptic generators of orders 2, 4, 6 and the Atkin–Lehner elements of norms 2, 3, 6 | medium |
| `SphereFactorAffine` | TEXTBOOK / GLUE | if `f, h : ℍ → P¹` are holomorphic, `f` is onto, the fibres are the same, and some point goes to `∞` under both, then `h = A∘f` with `A(z) = az+b`, `a ≠ 0` | `φ(f(τ)) := h(τ)` is injective with `φ(∞) = ∞`. It is holomorphic: by the local normal form `w ↦ w^m` of `f`, an `h` constant on the fibres of `f` is a holomorphic function of `w^m`. An injective holomorphic `φ : P¹ → P¹` fixing `∞` is affine (Ahlfors Ch. 4; Conway Ch. V; UNVERIFIED) | medium |
| `BaseChangeClassUnique` | GLUE | two base changes of `P/ℚ̄` along the same `ι : ℚ̄ → ℂ` have the same class in `M3 ℂ` | pullback uniqueness; the identity section goes to the identity section, so rigidity applies (Mumford §4 Cor. 1) | medium |
| `PiTwistC Y Φ π` | GLUE | `π(y) = π(y')` on `ℂ`-points iff the QM pairs are `Aut(𝒪)`-twists of each other | R2fp's fibre clause at `ℂ`-points: `X₆` is the coarse moduli space and `π` factors through `X₆/W`. For a pinned triple, qm-pin's comparison | medium-large |
| `QMTwistLattice` | GLUE | for `Q, Q'` that are `ι`-compatibly `ℂ²/Λ_τ`, `ℂ²/Λ_τ'`: twist-isomorphic iff `τ' ∈ Γ*τ` | the `Hom` form of T11a with GAGA; Skolem–Noether over `ℚ` (`α = u⁻¹(·)u`); `Tι(u)⁻¹` is a scalar; `1+i` (norm `−1`) fixes the sign | medium |
| `CMDescends` | LEAF candidate | a QM surface over `ℂ` with CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]` is, as a QM pair, the base change of one over `ℚ̄` with the same CM | Shimura–Taniyama 1961 and Shimura 1967 (CM abelian varieties and CM points are defined over `ℚ̄`); T11b for the CM; `A[3] ⊆ A(ℚ̄)` for the level (UNVERIFIED locators) | small-medium |
| `PiCMC Y Φ π` | GLUE, **proved** from `CMDescends`, `PiTwistC`, R1fp, R2fp, `BaseChangeClassUnique` | at `ℂ`-points with CM, `π = 0, ∞, −16/27` | `piCMC_of` | done |
| `CMFixedHasCM` | GLUE, **proved** from T11a | a fixed point of `ι(x)` gives CM | `cmFixedHasCM_of` | done |
| `OmegaSiegel`, `ThetaOmegaAnalytic` | GLUE, **proved** | `Ω(ℍ) ⊆ 𝔥₂`; the theta constants are holomorphic along `Ω` | `omegaSiegel_proof`, `thetaOmegaAnalytic_proof` | done |
| `S8Weight8`, `S8OrderCM3` | GLUE, **proved** from `S8WeightExact` | `\|G8\|` has weight 8; `ord_{i√3} G8 ≥ 2` | `s8Weight8_of`, `s8OrderCM3_of` | done |

**Leaves and the published statement.** `ValenceBoundGammaStar` is weaker than the published
formulas: it is an inequality and uses only `e_P ≤ 6`. Its hypothesis is an absolute-value
automorphy. That costs nothing: `F(γτ)/(j(γ,τ)^k F(τ))` is holomorphic of modulus one off the
zeros, hence a constant of modulus one, i.e. a unitary multiplier, and the valence formula holds for
those. Every other new Prop is glue.

**Which pieces each target uses.**
- `HauptmodulUnique` ⇐ `S8Nonzero`, `SphereFactorAffine`.
- `QMDenZeroCM3` ⇐ `S8Nonzero`, `S8WeightExact`, `ValenceBoundGammaStar`. The argument: suppose
  `Σθ⁸(Ω(τ₀)) = 0` and `τ₀` is not `Γ*`-equivalent to `i√3`. Then `T = {i√3, τ₀}` has
  `Σ ord ≥ 2 + 1 = 3 > 2 = m/2` with `m = 4`. If `τ₀` is `Γ*`-equivalent to `i√3`, conjugation
  finishes.
- `PeriodMapGlue` ⇐ (R1fp naturality), `BaseChangeClassUnique`, `PiTwistC`, `QMTwistLattice`,
  `PiCMC`, with `CMFixedHasCM` from T11a. At the own triple, `PiCMC` ⇐ `CMDescends` (with
  R2fp's CM clauses), so the moduli glue is `BaseChangeClassUnique`, `PiTwistC` and
  `QMTwistLattice`, plus the leaf candidate `CMDescends`.

## 3. Checks on the statements

All are model checks unless marked VERIFIED.

- **Verbatim (VERIFIED, `py/verbatim_check.py`).** `light_base.lean` contains ThetaPoint's `PkgI1`
  block (lines 77-289), and part_fqm's `QMHauptmodulFn`, `QMDenZeroCM3`, `IsHolP1At`,
  `GammaStarFibresCM`, `IsGammaStarHauptmodul`, `HauptmodulUnique`, character for character. The
  heavy file uses part_fqm itself (`PMBase.lean` = FibreQM's base and the current
  `part_fqm.lean`).
- **True, not vacuous.**
  - `HauptmodulUnique`: the reduction's hypotheses are true. The CM points exist (proved), and
    the holomorphy of the theta series is proved. The remaining analytic input is `Σθ⁸ ≢ 0`.
    Without it, `QMHauptmodulFn`'s value clause would be empty, and `f` could fail to be
    holomorphic. `S8Nonzero` closes that gap.
  - `QMDenZeroCM3`: the valence count is exactly saturated: weight 8 gives total `1/3`, and the
    double zero at the order-6 point `i√3` contributes `2/6`. This matches the numerical order
    `1.99992` and is (`jden_check.py`: both `Σθ⁸` and `∏θ`
    vanish at `i√3`; `|Σθ⁸|` lies between 7.7 and 108 at other sample points). The
    multiplier of `G8` is trivial (`py/multiplier.py`), which is what `s8OrderCM3_of` needs: with
    a non-trivial multiplier the order at `i√3` would be pinned only mod 6 up to the multiplier.
  - `PeriodMapGlue`: each glue Prop holds for the genuine `Y₃`, by the arguments in the table.
- **`OmegaSiegel` was only numerical before.** pkg-I1 had checked it numerically; it is now
  proved (`omegaSiegel_proof`).
- **A correction to fibre-qm-period's report (VERIFIED numerically).** Its §4 calls the weight-8
  form `S·dF⁴`. It is `S/dF⁴`. The formula printed there, `|S(γτ)/S(τ)| = |cτ+d|⁸|dF(τ)/dF(γτ)|⁴`,
  is right; it is its `detF'^(-4)` rows that give 1.0. With the normalization `det γ⁴`, the weight
  holds for the Atkin–Lehner elements too. So the valence argument runs on the full `Γ*` (total
  `1/3`, one orbit of the order-6 point). A second disc `−3` point and an inequivalence proof
  would not be needed.
- **A stale file in fibre-qm-period (VERIFIED).** The committed
  `scratch/fibre-qm-period/FibreQM.lean` predates part_fqm's last step: it lacks
  `qmSkolemNoetherC_proof` and `fibreQMPeriod_main`. `build_base.sh` here re-assembles the base
  from FibreQM's first 20634 lines and the current `part_fqm.lean`, and the result compiles
  (run_base2).

## 4. R1(b): comparison with r1b-state (`origin/wip/r1b-state`, 07669d97)

- **r1b-state's leaf.**
  `R1bState.R01b_ComplexUniformization' := ∃ Y Φ, R1fpProps Y Φ ∧ R1bProps Y Φ`. `R1bProps` has
  three clauses:
  - (a) every `P : QML3 ℂ` is QM-uniformized by some `Λ_τ`;
  - (b) a map `y : ℍ → Y(ℂ)` whose object at `τ` is `ℂ²/Λ_τ` with the torus's level structure
    `a ↦ [ι(a)(τ,1)ᵀ/3]`;
  - (c) every regular function on every Zariski open is holomorphic along `y`.

  It is intrinsic, says nothing about `π`, and pins `y(τ)` by the level structure.
- **fibre-qm-period's `R1bFamily Y Φ π`.** It asks only for an object at `yτ τ` that is
  `ι`-compatibly `ℂ²/Λ_τ`, and for `π ∘ yτ` to be continuous and holomorphic into `P¹`.
- **Verdict: use r1b-state's statement as the leaf.**
  - It is the published shape: Shimura's holomorphic `φ : ℍ → V(ℂ)` with its moduli
    interpretation, and Deligne's complex uniformization.
  - `R1bFamily` follows from it. Shapes: R1bProps' (b) gives the object; (c) gives holomorphy of
    `π ∘ y` (r1b-state's `q3_form_of_R1bProps`). The transfer to any triple with `R1fpProps` is
    `r1bProps_of_leaf`.
  - Two bridges are still needed:
    - bp-analytic's `Uniformization.IsUniformization` with `qmAct` must give the CPts-level
      `IsUniformization` with `IotaCompatible` used here;
    - `HolomorphicP1On` must give `IsHolP1At` and continuity.
- **Not compiled across the two files.** r1b-state works over the build modules (`PkgI3.AbVar`);
  this file works over ThetaPoint's scratch copy (`ZInQ.DefFaltings.AbVar`). r1b-state's §4 states
  that the two `AbVar` layers coincide in the build.
- **Integration recommendation.** Replace the hypothesis `R1bFamily (ownY h) (ownΦ h) (ownπ h)` of
  `fibreQMPeriod_periodMap` by r1b-state's `R01b_ComplexUniformization'` together with the bridge
  above. The bridge is glue, small to medium.
- **Overlap of the glue.** r1b-state's own reduction of `FibreQMPeriod'` uses four glue Props, and
  the pieces here refine them:
  - `FamilyHauptmodul` ≈ `PeriodMapGlue`'s fibre and CM part + `HauptmodulUnique`;
  - `PiOfQMLattice` ≈ `PiTwistC` (⇐) + `QMTwistLattice` (⇐);
  - `JDenNonzero` ≈ `QMDenZeroCM3` with `QMHauptmodul`'s `∞`-clause;
  - `UnifBaseChange` ≈ `CPtsTransport`.

## 5. Numerics (`scratch/period-map/py/`, mpmath at 40 digits, theta series `|n_k| ≤ 12`)

- **`al_weight.py`** (`al_weight_out.txt`):
  - `ι` is multiplicative on the basis (sympy);
  - the elements `j`, `2+i`, `2j+ij`, `1+j` normalize `𝒪`;
  - for each, `|G8(γτ)| det γ⁴ / (|cτ+d|⁸|G8(τ)|) = 1.0` at two points;
  - `Σθ⁸(Ω(√2+i)) = −33.9079295761…`.
- **`gen_check.py`:**
  - `1+i+j` (norm 2, order 4, fixes `√2+i`) gives ratio `1.0`;
  - the orders in `PSL₂` are 2 for `μ`, 4 for `1+i+j`, and 6 for `j(1+j)/2`.
- **`multiplier.py`:** the complex ratio `G8(γτ) det γ⁴/((cτ+d)⁸G8(τ))` is `1` for `(1+j)/2`,
  `j`, `i+j`, `3+2i`, `μ`, `1+i+j`, `2+i`.
- **`omega_sym.py`, `omega_lean.py` (sympy, exact):**
  - the closed form of `Ω`, its imaginary part, and `det Im Ω`;
  - the quotients by `√2² − 2` used in the Lean proof of `OmegaSiegel`.
- **`verbatim_check.py`:** the copied statements are verbatim.

## 6. Lean outcomes (all VERIFIED; outputs in `scratch/period-map/run_*.txt`)

| run | file | outcome |
|---|---|---|
| prereq | `lake build …QMLattice …JHeight …HeightConstant` | OK, 1m22s |
| run_base2 | `build_base.sh`: `PMBase.lean` (FibreQM lines 1-20634 + current `part_fqm.lean`) compiled to an olean with `lake env lean -o` | 0 errors, 2m49s, 47 axioms lines, none with `sorryAx` |
| run_light_full4 | `PMLight.lean` = `light_base.lean` + `part_light` + `part_theta` + `part_siegel` + `part_order` (imports Mathlib only), `lake env lean` | 0 errors, 16s; 17 axioms lines, all standard |
| run_heavy15 | `build_heavy.sh`: `DevHeavy.lean` = `import PMBase` + all parts + `part_heavy` | 0 errors; 22 axioms lines, all standard |
| run_full2 | `build_full.sh`: `PMFull.lean` = FibreQM base + `part_fqm` + all parts, one file, `lake env lean` | 0 errors, 3m13s; 69 axioms lines, none with `sorryAx` |

To reproduce, from the repository root:
1. build the prerequisites;
2. `scratch/period-map/build_base.sh`;
3. `lake env lean scratch/period-map/PMLight.lean`;
4. `scratch/period-map/build_heavy.sh`, or `build_full.sh` for the single-file check.

## 7. What remains

- **Glue, analysis on `ℍ`.**
  - `S8Nonzero`: a certified evaluation of ten genus-2 theta constants at `Ω(√2+i)`.
  - `S8WeightExact`: the modular embedding `γ ↦ M_γ ∈ Sp₄(ℤ)` for generators of `Γ*` with Igusa's
    leaf, plus the fact that those elements generate `Γ*`.
  - `SphereFactorAffine`: the local normal form, and injective holomorphic maps of `P¹`.
- **Glue, moduli.**
  - `BaseChangeClassUnique`: pullbacks and rigidity in Mumford's sense; the kernel's T11b is
    descent, not this.
  - `PiTwistC`: R2fp's fibre clause on `ℂ`-points. (`PiCMC` is reduced to `CMDescends`.)
  - `QMTwistLattice`: needs a `Hom` version of T11a.
- **Leaf.** `ValenceBoundGammaStar` (valence formula and the signature `(0;2,4,6)`): a human
  should check the locators.
- **R1(b).** Adopt r1b-state's statement and prove the bridge of §4.
- **Inherited caveat.** As for every Shimura-curve input, the SPECULATIVE premise bp-qmmoduli §2.2
  applies.
