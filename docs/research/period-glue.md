# period-glue: period-map's six glue Props — three proved, two reduced to leaves alone, one to leaves plus one AG glue Prop

Task period-glue, 2026-11-13. Base 6f296292 (contains origin/wip/period-map). Lean:
`scratch/period-glue/` (results log `log.md`). No file under `ZInQKernel/`, `blueprint/` or another
task's directory was edited. Model work only, no human review.

## 1. Result

**Verdict.** None of the six statements was changed. As far as model review can tell, all six are
true and not vacuous. Every theorem below compiles with no `sorry` and only the axioms
`[propext, Classical.choice, Quot.sound]` (VERIFIED, §7).

| Prop (period-map) | outcome | Lean |
|---|---|---|
| `S8Nonzero` | **PROVED** from Mathlib alone. It is a certified theta evaluation: `Re Σθ_m⁸(Ω(√2+i)) < 0` | `S8.lean`: `s8Nonzero_proof` |
| `BaseChangeClassUnique` | **PROVED** from Mathlib alone, using mul-rigidity's proof of rigidity (copied) | `BCU.lean`: `baseChangeClassUnique_proof` |
| `SphereFactorAffine` | **PROVED** from Mathlib alone. Three complex-analysis lemmas are proved on the way: the open mapping theorem for `ℍ → P¹`, removable singularities through a branched cover, and injective holomorphic maps of `P¹` | `SFA.lean`: `sphereFactorAffine_proof` |
| `S8WeightExact` | **REDUCED to two leaves, no glue left**: Igusa's `ThetaModularity` (pkg-I1, unchanged) and `GammaStarGen` (leaf candidate, §5.3) | `W8.lean`: `s8WeightExact_of` |
| `QMTwistLattice` | **REDUCED to one textbook leaf**, `T11aRiemannHom`, plus Skolem–Noether, which the kernel proves | `QMTwist.lean`: `qmTwistLattice_of'` |
| `PiTwistC` | **REDUCED to leaves plus one glue Prop.** The leaves are R1fp, R1hecke and R2fp (all three in the own-triple bundle) and T5 (`TorsionStructure`). One supporting fact is proved by mobius-glue (`AutOInnerFinite`). The remaining glue is `FibreTransferC`, a Jacobson-type transfer from `ℚ̄`- to `ℂ`-points | `PiTwist.lean`: `piTwistC_of`, `twistOrbitFinite_of'` |

```lean
theorem s8Nonzero_proof : S8Nonzero
theorem baseChangeClassUnique_proof : PeriodMapH.BaseChangeClassUnique
theorem sphereFactorAffine_proof : SphereFactorAffine
theorem s8WeightExact_of (hT : PkgI1.ThetaModularity) (hG : GammaStarGen) : S8WeightExact
theorem qmTwistLattice_of' (hH : T11aRiemannHom) (hSN : GlueDescent.LeafSkolemNoether) :
    QMTwistLattice
theorem piTwistC_of (Y Φ π) (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π)
    (hT : TwistOrbitFinite Y Φ) (hF : FibreTransferC Y π) : PiTwistC Y Φ π
theorem twistOrbitFinite_of' (Y Φ) (hH : R1heckeProps Y Φ) (hT : ObjBridge.TorsionStructure)
    (hA : AutOInnerFinite) : TwistOrbitFinite Y Φ
```

The namespace is `HSyn.G0Split.FibreQM.PeriodGlue`. Two hypotheses are proved outside this task:
- `GlueDescent.LeafSkolemNoether` is the kernel's definition, copied verbatim in the scratch base.
  The kernel proves it (`TSkolemKW.leafSkolemNoether`, `ZInQKernel/HDecomp/Textbook/SkolemNoether.lean`).
- `AutOInnerFinite` is mobius-glue's statement, copied verbatim; mobius-glue proves it
  (`scratch/mobius-glue/MobiusGlue.lean` §7-§8).

Neither proof can be imported next to the scratch copies, because the namespaces clash. At
integration each hypothesis is replaced by its theorem.

**End to end** (`fibreQMPeriod_periodGlue`, compiled in one file by `build_all.sh`). This is
period-map's `fibreQMPeriod_periodMap` with all six targets replaced as above. In addition,
`T11aRiemannEnd` is derived from `T11aRiemannHom`, and R1hecke is taken from the own-triple bundle:

```lean
theorem fibreQMPeriod_periodGlue (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hHom : T11aRiemannHom)
    (hCN : QMClassNumberOne) (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h))
    (hTors : ObjBridge.TorsionStructure) (hAI : AutOInnerFinite)
    (hFT : FibreTransferC (ownY h) (ownπ h))
    (hSN : GlueDescent.LeafSkolemNoether) (hD : CMDescends)
    (hTM : PkgI1.ThetaModularity) (hG : GammaStarGen)
    (hV : PeriodMap.ValenceBoundGammaStar) (hCP : CPtsTransport) : ThetaPt.FibreQMPeriod
```

- **Leaves:**
  - `R1R2fp`, `QMHauptmodul`, T35, `T11aRiemannHom`, `QMClassNumberOne`, `R1bFamily`;
  - T5 (`TorsionStructure`), `ThetaModularity`;
  - the candidates `CMDescends`, `GammaStarGen`, `ValenceBoundGammaStar`;
  - SN, which the kernel proves.
- **Glue proved by another task:** `MobiusGlue` (mobius-glue / image-plane) and
  `AutOInnerFinite` (mobius-glue).
- **Glue still open:** `FibreTransferC` and the inherited `CPtsTransport`.

**Effect on period-map's three targets.**
- `HauptmodulUnique ⇐ S8Nonzero, SphereFactorAffine`. Both are now theorems, so
  `HauptmodulUnique` is a theorem from Mathlib alone.
- `QMDenZeroCM3 ⇐ S8Nonzero, S8WeightExact, ValenceBoundGammaStar`. It now needs only leaves:
  `ThetaModularity`, `GammaStarGen` and `ValenceBoundGammaStar`.
- `PeriodMapGlue` at the own triple. It now needs:
  - the leaves R1fp, R1hecke, R2fp, T5, `T11aRiemannHom` and `CMDescends`;
  - SN and `AutOInnerFinite` (proved elsewhere);
  - the glue `FibreTransferC`.

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
- **The remaining input: generation.** `Γ* = ℚ^×·⟨g₄, g₆⟩` is `GammaStarGen` (§5.3).
  `py/triangle.py`: `x₂ = 2x₆x₄⁻¹ = (3/2)i + 2j + (1/2)ij` has `trd x₂ = 0`, so `g₆g₄⁻¹` has
  order 2.

### 2.4 `QMTwistLattice` (`QMTwist.lean`)

- **Reduction** (`qmTwistLattice_of`). `QMTwistLattice ⇐ T11aRiemannHom + QMLatticeTwistAlg`.
  - Isomorphisms `Q.q.twist α ≅ Q'.q` lift to linear automorphisms `M`, in both directions of the
    `Hom` leaf.
  - `M⁻¹M = 1` follows from `lift_unique`.
  - Equivariance follows from uniqueness of lifts.
- **`QMLatticeTwistAlg`** (pure algebra; `qmLatticeTwistAlg_of`, from SN):
  - **(⇐)** For `g = ι(x) ∈ Γ*`, take `α = x⁻¹(·)x` and `M = (cτ+d)⁻¹ι(x)`.
    `Λ_τ = {ι(b)v_τ : b ∈ 𝒪}` (`mem_qmLattice_iff`).
  - **(⇒)**
    - `α` is inner: extend it to `B` (mobius-glue's extension, copied), then SN.
    - `M∘ι(w)` commutes with `ι(i)`, `ι(j)`, so it is a scalar `p`.
    - `(τ', 1) = pι(x)(τ, 1)` with `x = w⁻¹b₁`.
    - `w⁻¹𝒪 ⊆ 𝒪x`, because `b ↦ ι(b)(τ,1)ᵀ` is injective.
    - `b₁ ∈ 𝒪^×`, so `x` normalizes `𝒪`.
    - `det ι(x) > 0` follows from `moebius_im`.

### 2.5 `SphereFactorAffine` (`SFA.lean`)

- **Reduction** (`sphereFactorAffine_of`). Set `φ := h ∘ f⁻¹`. It is well defined, injective and
  fixes `∞`. It is continuous because `f` is open; this uses `continuousAt_of_isHolP1At`
  (holomorphy into `P¹` implies continuity).
- **`HolP1OpenMap`** (`holP1OpenMap_proof`).
  - In charts, `g = C ∘ G` with `C ∈ {coe, 1/·}` and `G` analytic.
  - The set where `g` is locally constant is clopen, by the identity theorem on chart balls. Since
    `ℍ` is connected, `g` is nowhere locally constant.
  - Mathlib's `AnalyticAt.eventually_constant_or_nhds_le_map_nhds` then gives openness.
- **`SphereInjAffine`** (`sphereInjAffine_proof`).
  - `f = φ|ℂ` is entire and injective. Pick `z₁` with `f'(z₁) ≠ 0`.
  - Then `r(z) = (z−z₁)/(f(z)−f(z₁))` is entire. Near `∞`, `f = 1/G(1/z)`, so `r → G'(0)`.
  - By Liouville, `r` is constant, so `f` is affine.
- **`HolP1FactorHol`** (`holP1FactorHol_proof`).
  - `core_removable`: if `Ψ ∘ A = H` with `A, H` analytic, `A` nonconstant and `Ψ` continuous,
    then `Ψ` is analytic.
  - Off the isolated critical points of `A`, Mathlib's `analyticAt_comp_iff_of_deriv_ne_zero`
    (an analytic local inverse) applies. The open mapping theorem covers a punctured
    neighbourhood, and the removable singularity theorem finishes.
  - It is applied in the charts of `P¹`.

### 2.6 `PiTwistC` (`PiTwist.lean`)

- **Reduction** (`piTwistC_of`). `PiTwistC ⇐ R1fp, R2fp, TwistOrbitFinite, FibreTransferC`.
  - On `ℚ̄`-points: the R2fp fibres equal the twist classes, which equal the `G`-orbits.
  - `FibreTransferC` carries this to `ℂ`-points.
  - On `ℂ`-points, `TwistOrbitFinite` turns the `G`-orbits back into twist classes.
- **`TwistOrbitFinite`** (`twistOrbitFinite_of'`). Take `G = {g_t ∘ h_u : t ∈ T, u ∈ U}`:
  - `g_t`, `h_u` are R1hecke's automorphisms;
  - `T` is a finite set of representatives of `Aut 𝒪` mod inner (`AutOInnerFinite`);
  - `U` is a finite set of units representing classes mod `3𝒪` (`unitReps`).
  - (⇒) A twist isomorphism, composed with `ι(v)` (`conjUnitIso'`), becomes a QM isomorphism
    `Q.q.twist t ≅ Q'.q`. The level structures differ by right multiplication by some
    `u₀ ∈ 𝒪` invertible mod 3 (the kernel's `Level3.torsor`, from T5). `u₀` lifts to a unit
    (`UnitLiftMod3`) and then to a representative in `U`. `Φ` is injective, which gives
    `y' = y ≫ g_t ≫ h_u`.
  - (⇐) Forget the level structure.
- **`UnitLiftMod3`** (`unitLiftMod3_proof`, a finite computation).
  - `nrd` is multiplicative (`nrdZ_mulCoord`), so `u₀` invertible mod 3 gives `3 ∤ nrd(u₀)`.
  - A table of 72 units with coordinates at most 3 (`py/unit_table.py`) covers every class with
    `nrd ≢ 0 mod 3`. `decide` checks it over the 81 classes (`unitTbl_spec`).

## 3. The new named Props

| Prop | kind | statement (informal) | status |
|---|---|---|---|
| `GammaStarGen` | **LEAF candidate** (flagged, §5.3) | `Γ* ⊆ ⟨ι(1+i+j), ι((j−3)/2), ℚ^×⟩` | signature `(0;2,4,6)` + Poincaré + covolume; numerically checked on 30 independent elements |
| `T11aRiemannHom` | **LEAF** (textbook) | analytic representation of `Hom(A, A')` for uniformized `A, A'/ℂ` | Mumford §1, Birkenhake–Lange Prop. 1.2.1, GAGA (UNVERIFIED locators). The kernel's `T11aRiemannEnd` is its case `A = A'` (`t11aRiemannEnd_of_hom`) |
| `FibreTransferC Y π` | **GLUE (AG)**, open; split into `ToP1AgreeC` and `FibreGenericC` | for `Y` proper smooth over `ℚ`: fibres of `π` = `G`-orbits on `ℚ̄`-points ⇒ on `ℂ`-points | §4 |
| `ToP1AgreeC Y` | GLUE (AG, textbook density), open | two maps `Y → P¹` agreeing on `ℚ̄`-points agree on `ℂ`-points | §4 |
| `FibreGenericC Y π` | GLUE (AG), open | (⇒) half of `FibreTransferC` | §4 |
| `AutOInnerFinite` | glue, proved by mobius-glue | `Aut 𝒪` is finite mod conjugation by `𝒪^×` | copy of mobius-glue's statement |
| `QMLatticeTwistAlg` | glue, **PROVED** (from SN) | twist relation on QM lattices ⇔ `τ' ∈ Γ*τ` | §2.4 |
| `TwistOrbitFinite Y Φ` | glue, **PROVED** from R1hecke, T5, `AutOInnerFinite` | twist relation = orbits of a finite `G ⊆ Aut(Y)` (`ℚ̄`, `ℂ`) | §2.6 |
| `UnitLiftMod3` | glue, **PROVED** | `𝒪^× → (𝒪/3𝒪)^×` onto | §2.6 |
| `HolP1OpenMap`, `HolP1FactorHol`, `SphereInjAffine` | glue, **PROVED** | §2.5 | §2.5 |
| `S8Omega0` | glue, **PROVED** | `Σθ⁸(Ω₀) ≠ 0` | §2.1 |

**Checks on the statements** (model checks):
- `FibreTransferC` carries `IsProper Y.hom` and `SmoothOfRelativeDimension 1 Y.hom` as hypotheses.
  Without them it is false: `Y = Spec ℂ` has no `ℚ̄`-points.
- `T11aRiemannHom` is the published `Hom` statement, and its `End` case is the kernel's leaf
  verbatim.
- The P¹-holomorphy notions `IsHolC1At` and `IsHolSphere` (chart form) have the same shape as
  fibre-qm-period's `IsHolP1At`. All three lemmas built on them are proved, so no new leaf rests
  on these definitions.

## 4. What remains: `FibreTransferC` (AG glue) and how to prove it

**Split** (`fibreTransferC_of`, compiled). `FibreTransferC ⇐ ToP1AgreeC + FibreGenericC`.
- `ToP1AgreeC` covers (⇐). It is the textbook density statement: two maps to `P¹` that agree on
  `ℚ̄`-points of a reduced finite-type `ℚ`-scheme agree on `ℂ`-points. It is applied to `π ∘ g`
  and `π`.
- `FibreGenericC` is the hard half (⇒). Its hypothesis forces `π` to be non-constant on every
  component, since `G`-orbits are finite and a component has infinitely many `ℚ̄`-points.
  - Over closed points it reduces to `ℚ̄`.
  - Over generic points of components it needs the Jacobson argument below.

Both halves are needed: period-map's `periodMapGlue_of` uses the full iff for the fibre clause.

**Statement.** `Y` is proper smooth of relative dimension 1 over `ℚ`, and `G` is a finite set of
automorphisms. If the fibres of `π` on `ℚ̄`-points are the `G`-orbits, then the same holds on
`ℂ`-points.

**Model proof.**
1. Let `E = {(p,q) ∈ Y ×_ℚ Y : π(p) = π(q)}`, the equalizer of `π∘pr₁` and `π∘pr₂`. It is closed,
   since `P¹` is separated.
2. Let `Γ = ⋃_{g∈G} graph(g)`. It is closed, since `Y` is separated and `G` is finite.
3. Both are closed in the finite-type `ℚ`-scheme `Y×Y`, which is Jacobson. So each is the closure
   of its closed points.
4. Closed points are images of `ℚ̄`-points. On these `E` and `Γ` agree by hypothesis, so `E = Γ`.
5. A `ℂ`-point lies in `E` iff `π(y) = π(y')`. It lies in `Γ` iff it factors through some
   `graph(g) ≅ Y`, which is reduced because `Y` is smooth.

**What is needed in Lean.**
- Turn the charts of `ToP1` into a morphism to `P¹`, or work chart by chart.
- Equalizers and graphs as closed subschemes.
- Jacobson density of closed points, using Mathlib's `JacobsonSpace`.

Size: medium-large. An alternative is to split the `ℂ`-points by the image point: closed points
reduce to `ℚ̄` through one embedding `ℚ̄ → ℂ`, and generic points of components need the
function-field form of the statement.

## 5. The two flagged leaves, restated, plus `GammaStarGen`

Locators are from memory (no network): UNVERIFIED. A human should check each one against the
printed source.

### 5.1 `ValenceBoundGammaStar` (period-map, unchanged)

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
     Tokyo 24 (1977): its table of the 85 arithmetic triangle groups lists `(2, 4, 6)` with the
     quaternion algebra over `ℚ` ramified at `{2, 3}` (the table entry was not read);
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

### 5.2 `CMDescends` (period-map, unchanged)

The Lean statement:

> a level-3 QM surface `Q/ℂ` with CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`) is, as a QM pair,
> isomorphic to the base change along some `ι : ℚ̄ → ℂ` of a level-3 QM surface `P/ℚ̄` with the
> same CM.

**Published statements.**
1. **CM abelian varieties are defined over `ℚ̄`.** An abelian variety over `ℂ` of CM type is
   isomorphic to the base change of one defined over a number field.
   - Shimura–Taniyama, *Complex multiplication of abelian varieties and its applications to
     number theory* (1961);
   - Shimura, *Abelian varieties with complex multiplication and modular functions* (1998), §12
     (models over number fields);
   - no proposition number is given: the numbers recalled from memory could not be checked
     offline. UNVERIFIED.
   - It applies: `HasCM4` gives an endomorphism `φ` commuting with `ι(𝒪)`, `φ² = −1`. So
     `End⁰(A)` contains `B ⊗ ℚ(i)`, `A` is isogenous to `E²` with `E` CM, and `A` is of CM type.
2. **Endomorphisms are rigid.** For abelian varieties over an algebraically closed field `k` of
   characteristic 0 and `k ⊆ K`, `Hom_k(A,B) = Hom_K(A_K,B_K)`. This is the kernel's T11b
   (Mumford; Conrad, *Chow's K/k-image and K/k-trace*; theorem number UNVERIFIED). It carries `ι`
   and the CM endomorphism down to `ℚ̄`.
3. **The level structure descends.** `A[3](ℚ̄) = A[3](ℂ)`, both of order `3⁴`.

**Derivation.** Take `A₀/ℚ̄` with `(A₀)_ℂ ≅ Q.A`. Transport `ι` and the CM endomorphism by (2), and
the level structure by (3). The composite iso gives `IsBaseChangeOf`.

**What the human should check.**
- The CM-type hypothesis in Shimura–Taniyama: `End⁰ ⊇` a CM field of degree `2 dim`.
- That (1) is stated for abelian varieties up to isomorphism, not up to isogeny.

### 5.3 `GammaStarGen` (new, LEAF candidate)

**Statement.** `∀ γ ∈ Γ*, γ ∈ ⟨ι(1+i+j), ι((j−3)/2), ℚ^×·1⟩`.

**Sources.** The signature of §5.1(2), and Poincaré's polygon theorem (Beardon, *The geometry of
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

**Numerical check** (`py/gen_check.py`, VERIFIED). The sample is the first 30 elements of
`N(𝒪)⁺` with coordinates `|n_k| ≤ 4` in N5's basis and `nrd ∈ {1,2,3,6}`, found by a search that
is independent of the generators. Greedy reduction of `cosh d(γp, p)` by the vertex stabilizers
`⟨g₄⟩`, `⟨g₆⟩`, `⟨g₂⟩` brings all 30 to a rational scalar.



## 6. Numerics (`scratch/period-glue/py/`)

- `s8_value.py`, `s8_exact.py`: `Ω(√2+i)` exact; `θ_m(Ω₀)⁸/ϑ₀₀(i)¹⁶ ∈ {−¼, −1, −4, 0}`;
  `Σθ⁸(Ω₀) = −9ϑ₀₀(i)¹⁶`; truncation tail bounds.
- `omega0_lc.py`: the `linear_combination` coefficients for `Ω(√2+i) = Ω₀`.
- `modemb.py`: exact `M ∈ Sp₄(ℤ)` for `g₂ = μ`, `g₄`, `g₆`, and the factor ratio `±1`.
- `w8_lc.py`, `w8_lean.py`: the polynomial identities for `g₄`, `g₆` and their coefficients.
- `triangle.py`: `x₂ = (3/2)i + 2j + (1/2)ij` with `x₂x₄ = 2x₆`.
- `gen_check.py`: the 30-element generation check.
- `unit_table.py`: the 72-unit table.

## 7. Lean outcomes (VERIFIED; outputs `scratch/period-glue/run_*.txt`)

| run | file | outcome |
|---|---|---|
| run_prereq | `lake build …QMLattice …JHeight …HeightConstant …Objects` | OK, 1m25s |
| run_base1 | `build_base.sh`: `PGBase.lean` = FibreQM 1-20634 + part_fqm + period-map's parts (= DevHeavy content), `lake env lean -o` | 0 errors, 3m13s |
| run_light_base | `build_light.sh`: `PGLight.lean` = period-map's PMLight.lean | 0 errors, 1m25s |
| run_bcu | `BCU.lean` (PGBase) | 0 errors; standard axioms |
| run_qmtwist | `QMTwist.lean` (PGBase) | 0 errors; `qmTwistLattice_of`, `qmLatticeTwistAlg_mpr`, `qmTwistLattice_of'` standard axioms |
| run_pitwist | `PiTwist.lean` (PGBase) | 0 errors; `piTwistC_of`, `fibreTransferC_of`, `unitLiftMod3_proof`, `twistOrbitFinite_of` standard axioms |
| run_s8 | `S8.lean` (PGLight) | 0 errors; `s8Nonzero_iff`, `s8Nonzero_proof` standard axioms |
| run_w8 | `W8.lean` (PGLight) | 0 errors; `s8WeightExact_of` standard axioms |
| run_sfa | `SFA.lean` (PGLight) | 0 errors; `holP1OpenMap_proof`, `holP1FactorHol_proof`, `sphereInjAffine_proof`, `sphereFactorAffine_proof` standard axioms |
| run_all | `build_all.sh`: `PGAll.lean` = import PGBase + all six files + `final_part.lean` | 0 errors, exit 0; the eight printed theorems, among them `fibreQMPeriod_periodGlue`, standard axioms |

**To reproduce,** from the repository root:
1. the prereq build;
2. `scratch/period-glue/build_base.sh` and `scratch/period-glue/build_light.sh`;
3. `scratch/period-glue/check.sh scratch/period-glue/<File>.lean`, or
   `scratch/period-glue/build_all.sh`.

The base files are verbatim assemblies of fibre-qm-period's and period-map's committed files.
They are gitignored and rebuilt by the scripts.

**Copies.** These are copied verbatim from other tasks' scratch files, with the source named at
each copy:
- rigidity (mul-rigidity);
- the `Aut 𝒪` extension, `transportLevel` and `conjUnitIso` (mobius-glue).

Scratch files cannot import each other.
