# height-dict: the kernel's Faltings height is the printed one

**Result (VERIFIED: compiled; every theorem below has the axioms `propext`, `Classical.choice`,
`Quot.sound`).** The 11-16 dictionary pass gave three reasons for rating `bostLowerBound` and
`gaudronRemondThm14` as consequences:

1. the analytic uniformization is biholomorphic onto `A^an`;
2. the torus integral of `|ω ∧ ω̄|`;
3. `ω = e*Ω¹` (EGA IV 17.2.5).

All three are now Lean theorems. Both rows are restated over a printed stable height,
`ZInQ.HeightDict.IsPrintedStableHeight`, which is built as the print builds it:

- **Néron model**: the Néron model over a field with semistable reduction.
- **Invariant differential**: `ω = ⋀^g Γ(S, e*Ω¹_{𝒩/S})`, computed from the stalks
  `𝒪_{S,s} ⊗ Ω[𝒪_{𝒩,e(s)}/𝓞_L]` (Mathlib's Kähler differentials).
- **Complex volume**: `(i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄`, defined as the total mass of the invariant measure on the
  compact group `A_τ(ℂ)` with its analytic topology, normalized at the identity in algebraic coordinates.

No uniformization enters the definition. Both consumer forms are proved from the restated leaves. Besides
the leaves, the proofs read only the existing textbook fields `uniformizationLeafAll` and
`mumfordTorsionAlgClosed` (which give T35):

```lean
theorem ZInQ.HeightDict.bostLowerBound_of_printed (hB : BostLowerBoundPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : ZInQ.HeightSplit.BostLowerBound
theorem ZInQ.HeightDict.gaudronRemondThm14_of_printed (hGR : GaudronRemondThm14Printed)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : ZInQ.HeightSplit.GaudronRemondThm14
```

The printed height **coincides** with the kernel's. Given T35, the restated leaves are therefore equivalent
to the old ones, but they are now stated over a definition a reader can check against the print:

```lean
theorem ZInQ.HeightDict.isPrintedStableHeight_iff (hU : AnalyticUniformizationUnique)
    (hDim : UniformizationDim) (hMet : NeronMetrizable) [NumberField K] (A : PkgI3.AbVar K) (x : ℝ) :
    IsPrintedStableHeight A x ↔ IsStableFaltingsHeight A x
```

Three faithfulness checks are also proved:

- The printed metric is not vacuous: a normalized invariant measure exists (`exists_isNormalizedBy`).
- For `η ≠ 0` the printed metric has exactly one value, the kernel's `|c_τ η|² covol(Λ_τ)`
  (`isFaltingsMetricSq_iff`).
- The printed lattice is the kernel's `detLattice` (`printedDetLattice_eq`, from
  `Conormal.printedOmega_eq`).

**Target: both rows back to LEAF.** Both new leaves are the old statements with the definition of `h`
replaced by a printed one. Each is rated printed form (§6). The definition-level readings that remain are
listed in §4 (R1-R3). None of them is a theorem step of the kind the 11-16 pass objected to. The autofold
dry run of the fold compiles. It is −2 GLUE if the rows were rated consequence; the strict count is unchanged
against this base's `kinds.tsv`, which still has them as LEAF.

**Which route is shorter.** Route (a) was taken, and it delivers (b) as well. Route (b) alone ("restate
over a printed definition, prove the consumer form") is not shorter: the consumer forms are over the kernel's
height, so proving them from restated leaves needs exactly "printed ⇒ kernel", which is (a). The cost lay
in two places:

1. Stating the printed integral without Mathlib support for integrating forms on manifolds. The solution is
   the invariant-measure characterization (§2), so no manifold atlas is needed.
2. Two Mathlib 4.35 gaps:
   - "holomorphic ⇒ `C¹`" in several variables (`Holomorphic.lean`);
   - the volume of a compact group uniformized by `ℂ^g/Λ` (`TorusVolume.lean`).

## 1. `GroupModel.height` and the docstring argument for its faithfulness

Read (VERIFIED) in `ZInQKernel/HDecomp/Faltings/{Models,HodgeData,Height}.lean`:

- `GroupModel.height 𝒢 = ⨅ (g) (M : MetrizedModel A L g) (_ : M.model = 𝒢), M.hodge.modelHeight`
  (Height.lean:235).
- `modelHeight = deg(ω̄)/[L:ℚ]` with `deg = log #(M/𝓞η) − Σ_τ log ‖η‖_τ` (HodgeData.lean:391,
  `modelHeight_eq`).
- `‖η‖²_τ = torusMetricSq (periods τ) (coeff τ η) = |coeff τ η|² · covol(periods τ)` (HodgeData.lean:268, 365).
- `MetrizedModel.arch` (Height.lean:30-40) pins the archimedean data:
  - `periods τ` is the kernel `Λ` of a `𝒢.IsAnalyticUniformization τ Λ Φ` (Models.lean:206: `Φ : ℂ^g → 𝒢(ℂ)_τ` is
    a surjective homomorphism with kernel `Λ`, each `Φ⁻¹(U(ℂ))` is open, and regular functions are
    `ℂ`-differentiable along `Φ`);
  - `coeff τ (wedge f) = jacDet Φ f = det(∂(fᵢ ∘ Φ)/∂z_j(0))`.
- `lattice_eq` pins the lattice to `detLattice g`, which is `⋀^g` of `omega = ⋂_s omegaAt s`. Here
  `omegaAt s` is the `𝓞_L`-span of the classes of `I_{e(s)}` in `𝔪_ξ/𝔪_ξ²` (Models.lean:125-160).

The docstrings argue faithfulness in three places:

- Models.lean §17: `Φ` is a homeomorphism `ℂ^g/Λ ≅ A_τ(ℂ)`, "holomorphic, hence biholomorphic ... STANDARD
  facts of complex analysis, not proved here".
- HodgeData.lean, `torusMetricSq`: "`‖η‖² = (i/2)^g ∫_{ℂ^g/Λ} η ∧ η̄ = |c|² · covol(Λ)`".
- Models.lean §16: "the image of `I_x` in `𝔪_ξ/𝔪_ξ²` is the stalk at `s` of the conormal sheaf
  `e*(I/I²) = e*Ω¹_{𝒢/S}` (EGA IV 17.2.5, UNVERIFIED)", and the global sections are the intersection of the
  stalks.

These are exactly the three steps of the 11-16 ruling.

## 2. The printed height (Lean)

From `ZInQKernel/Contrib/OneProof/HeightDictionary.lean` and `.../HeightDictionary/Conormal.lean`:

```lean
-- Conormal.lean (namespace ZInQ.HeightDict.Conormal; local instances: 𝓞_L → 𝒪_{𝒢,ξ} the structure
-- map, 𝒪_{𝒢,ξ} → 𝒪_{S,η} the stalk map of the unit section)
noncomputable def theta : 𝒢.cotangent →ₗ[𝒢.genStalk] (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L] :=
  kerCotangentToTensor (𝓞 L) 𝒢.genStalk (Reta L) ∘ₗ
    Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒢.genStalk)
      (RingHom.ker (algebraMap 𝒢.genStalk (Reta L))) (AlgHom.id 𝒢.genStalk 𝒢.genStalk)
      (maximalIdeal_le_ker 𝒢)
noncomputable def printedOmegaAt (s : Spec (CommRingCat.of (𝓞 L))) :
    Submodule (𝓞 L) ((Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]) :=
  Submodule.span (𝓞 L) (Set.range fun b : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s) =>
    (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s b))
noncomputable def printedOmega : Submodule (𝓞 L) 𝒢.cotangent :=
  (⨅ s, printedOmegaAt 𝒢 s).comap (theta' 𝒢)

-- HeightDictionary.lean (namespace ZInQ.HeightDict)
noncomputable def anBorel (𝒢 : GroupModel A L) (τ : L →+* ℂ) : MeasurableSpace (𝒢.Pts τ) :=
  @borel _ (anTop 𝒢 τ)
noncomputable def coordMap (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (U : Fin g → 𝒢.G.left.Opens) (s : ∀ i, Γ(𝒢.G.left, U i)) : 𝒢.Pts τ → (Fin g → ℂ) :=
  fun p i => 𝒢.evalAt p (U i) (s i)
def IsNormalizedBy (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (mu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) : Prop :=
  letI := anTop 𝒢 τ
  letI := anBorel 𝒢 τ
  ∀ (U : Fin g → 𝒢.G.left.Opens) (hU : ∀ i, 𝒢.genericUnit ∈ U i) (s : ∀ i, Γ(𝒢.G.left, U i))
    (hm : ∀ i, 𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk)
    (l : L), eta = l • 𝒢.wedge (fun i => ⟨_, hm i⟩) →
    ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 (1 : 𝒢.Pts τ), ∀ E ⊆ W, MeasurableSet E →
      |(mu E).toReal - ‖τ l‖ ^ 2 * (volume (coordMap 𝒢 τ U s '' E)).toReal| ≤
        ε * (volume (coordMap 𝒢 τ U s '' E)).toReal
def IsFaltingsMetricSq (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (eta : 𝒢.hodgeSpace g) (r : ℝ) :
    Prop :=
  letI := anTop 𝒢 τ
  letI := anBorel 𝒢 τ
  ∀ mu : Measure (𝒢.Pts τ), IsFiniteMeasure mu → mu.IsMulLeftInvariant → IsNormalizedBy 𝒢 τ mu eta →
    (mu univ).toReal = r
noncomputable def printedDetLattice (𝒢 : GroupModel A L) (g : ℕ) :
    Submodule (𝓞 L) (𝒢.hodgeSpace g) :=
  Submodule.span (𝓞 L) (Set.range fun v : Fin g → Conormal.printedOmega 𝒢 =>
    (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => (v i : 𝒢.cotangent)))
def IsPrintedStableHeight {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (𝒩 : GroupModel A L) (g : ℕ),
    𝒩.IsNeronModel ∧ IsSemistable 𝒩 ∧ A.dim = (g : WithBot ℕ∞) ∧
    ∃ eta ∈ printedDetLattice 𝒩 g, eta ≠ 0 ∧ secIndex (printedDetLattice 𝒩 g) eta ≠ 0 ∧
      ∃ r : (L →+* ℂ) → ℝ, (∀ τ, IsFaltingsMetricSq 𝒩 τ eta (r τ)) ∧
        x = (Real.log (secIndex (printedDetLattice 𝒩 g) eta) -
          (1 / 2) * ∑ τ : L →+* ℂ, Real.log (r τ)) / Module.finrank ℚ L
```

**Objects.** Every object is Mathlib's or the kernel's:

- Mathlib: `KaehlerDifferential` (`Ω[·⁄·]`, `D`), `kerCotangentToTensor`, `Ideal.mapCotangent`, stalks and
  stalk maps, `Measure`, `IsMulLeftInvariant`, `volume` on `ℂ^g` (Lebesgue `dx₁dy₁⋯dx_gdy_g`), `borel`.
- The kernel: `anTop` (TailZ.lean:875, the analytic topology of `𝒢(ℂ)_τ`, Hausdorff by the proved
  `analyticPointsT2`), `wedge`, `hodgeSpace`, `secIndex`, `IsNeronModel`, `IsSemistable`.

**Reading the definitions.**

- `printedOmegaAt s` is the image of `(e*Ω¹)_s = 𝒪_{S,s} ⊗_{𝒪_{𝒢,e(s)}} Ω[𝒪_{𝒢,e(s)}/𝓞_L]` in the generic
  fibre `𝒪_{S,η} ⊗_{𝒪_{𝒢,ξ}} Ω[𝒪_{𝒢,ξ}/𝓞_L]`. It is spanned by the `1 ⊗ d(b|_ξ)`. Over `𝓞_L` that span already
  equals the `𝒪_{S,s}`-span, by the Leibniz rule and because `t ∉ s` is a unit at `e(s)`.
- `printedOmega` pulls back along the canonical map `θ`, `df ↦ 1 ⊗ df`, which is proved injective. It takes
  the intersection over `s`: the global sections of a lattice are the intersection of its stalks.
- `IsNormalizedBy mu η` says that `mu` is the measure `(i/2)^g η ∧ η̄` at the identity. Take any regular
  functions `f₁, …, f_g` vanishing at the origin with `η = l · df₁ ∧ ⋯ ∧ df_g`. Then the image of `mu` under
  `F = (f₁, …, f_g)` has density `|τ(l)|²` at `F(1)` relative to Lebesgue measure, since
  `(i/2) dz ∧ dz̄ = dx ∧ dy`.
- `IsFaltingsMetricSq η r` says that every finite left-invariant measure that is `(i/2)^g η ∧ η̄` at the
  identity has total mass `r`.
- Sign: `(i/2)^g ∫ η ∧ η̄` is read as the positive measure `|h|² dλ`. This is the convention that makes
  the metric positive, and the kernel's `torusMetricSq` docstring uses the same reading.

## 3. What is proved (all VERIFIED)

New files, all under `ZInQKernel/Contrib/OneProof/` (76 KB in total); nothing else under `ZInQKernel/` was
edited. `lake build ZInQKernel.Contrib.OneProof.HeightDictionary` succeeds.

| file | content |
| --- | --- |
| `HeightDictionary/TorusVolume.lean` (Mathlib only) | `exists_fundamentalDomain_ball` (a fundamental domain of `Λ` containing a ball `B` with `(B − B) ∩ Λ = 0`); `IsUnif.torusHomeo` (`ℂ^g/Λ ≃ₜ G`); `IsUnif.isTopologicalGroup`, `compactSpace`, `secondCountable`; `IsUnif.piMeasure_*` (`π = Φ_*(Lebesgue|_D)` is finite, left-invariant and open-positive, i.e. Haar; it is independent of `D`; `π(Φ(B_r)) = λ(B_r)`); **`volume_eq_of_normalized`**; `piMeasure_normalized` (existence) |
| `HeightDictionary/Holomorphic.lean` (Mathlib only) | **`hasStrictFDerivAt`**: `ℂ`-differentiable on an open subset of `ℂ^g` ⇒ strictly differentiable. Each partial derivative is the Cauchy integral `(2πi)⁻¹ ∮ t⁻² f(z + tv) dt`, which is continuous in `z`. Mathlib 4.35 has this only for `ℂ → E`, and the kernel's `IsAnalyticUniformization` gives only `DifferentiableOn ℂ` |
| `HeightDictionary/Conormal.lean` (imports `HeightBC.OmegaBC`) | stalk-map compatibilities (`unitStalk_stalkAlg`, `specMap_stalkAlg`); `theta`, `theta'`; **`omegaAt_map`** (`(omegaAt s).map θ = printedOmegaAt s`); **`theta_injective`** (a section `𝒪_{S,η} → 𝒪_{𝒢,ξ}/I²` built with `IsLocalization.liftAlgHom`, then Mathlib's `retractionKerCotangentToTensorEquivSection`); `omega_map`; **`printedOmega_eq`** |
| `HeightDictionary.lean` | the definitions of §2; `BostLowerBoundPrinted`, `GaudronRemondThm14Printed`; `printedDetLattice_eq`, `isFaltingsMetricSq_of_metrized`, `det_fderiv_coordMap`, `hasStrictFDerivAt_coordMap`, `exists_isNormalizedBy`, `isFaltingsMetricSq_iff`, `isPrintedStableHeight_of`, `isStableFaltingsHeight_of_printed`, `isPrintedStableHeight_iff`, `bostLowerBound_of_printed(')`, `gaudronRemondThm14_of_printed(')` |

The core archimedean lemma:

```lean
theorem TorusVolume.volume_eq_of_normalized (h : IsUnif Λ Φ) (μ : Measure G) [IsFiniteMeasure μ]
    [μ.IsMulLeftInvariant] (F : G → (Fin g → ℂ)) (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    (hψ : HasStrictFDerivAt (F ∘ Φ) (D.restrictScalars ℝ) 0) (a : ℝ)
    (hnorm : ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 (1 : G), ∀ E ⊆ W, MeasurableSet E →
      |(μ E).toReal - a * (volume (F '' E)).toReal| ≤ ε * (volume (F '' E)).toReal) :
    (μ univ).toReal =
      a * ‖LinearMap.det (D : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 * ZLattice.covolume Λ
```

Here `G` is a Hausdorff group and `IsUnif Λ Φ` says that `Φ` is a continuous surjective homomorphism whose
kernel is the full lattice `Λ`. Proof:

1. `G` is the compact topological group `ℂ^g/Λ` transported along the homeomorphism.
2. `μ = c π` by Mathlib's `isMulLeftInvariant_eq_smul`.
3. Choose a fundamental domain containing a small ball. Then `μ(Φ(B_r)) = c λ(B_r)`.
4. By Mathlib's Jacobian estimates, `λ(F(Φ(B_r))) ≈ |det_ℝ D| λ(B_r) = |det_ℂ D|² λ(B_r)`.
5. The normalization forces `c = a |det D|²`. Then `μ(G) = c λ(D) = c covol(Λ)`.

Applied to `G = 𝒢(ℂ)_τ` with `anTop`, `Φ` from `M.arch` and the algebraic coordinates `F`, this gives
`|τ(l) det D|² = |τ(l) jacDet Φ f|² = |coeff_τ η|²`. The steps use `germAlong_eventuallyEq`, `fderiv_pi` and
the `arch` clause. That is `isFaltingsMetricSq_of_metrized`: the kernel's `torusMetricSq Λ (coeff τ η)` is
the printed metric.

`#discharges` (VERIFIED; full output in `scratch/height-dict/discharges.txt`, built on this base):

```
DISCHARGES [OpenResearchLeaves26.bostLowerBound] by ZInQ.HeightDict.bostLowerBound_of_printed
  still assumes: [ZInQ.HeightDict.BostLowerBoundPrinted,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.gaudronRemondThm14] by ZInQ.HeightDict.gaudronRemondThm14_of_printed
  still assumes: [ZInQ.HeightDict.GaudronRemondThm14Printed,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 56 open hypotheses, 2963 theorems checked, 11 discharge one
```

The output also lists the `'` variants. They assume the kernel Props `AnalyticUniformizationUnique` and
`UniformizationDim` instead of the two fields.

The other two height-split rows over `IsStableFaltingsHeight` are handled the same way: verbatim
restatements `JavanpeykarBoundPrinted` and `PazukiCor13UpperPrinted`, with `javanpeykarBound_of_printed` and
`pazukiCor13Upper_of_printed`. `#discharges` lists them as well:

```
DISCHARGES [OpenResearchLeaves26.javanpeykarBound] by ZInQ.HeightDict.javanpeykarBound_of_printed
DISCHARGES [OpenResearchLeaves26.pazukiCor13Upper] by ZInQ.HeightDict.pazukiCor13Upper_of_printed
```

Each still assumes its printed leaf, `UniformizationLeafAll` and `MumfordTorsionAlgClosed`, with standard
axioms. The total line reads `13 discharge one`.

**Autofold.** The spec is `scratch/height-dict/autofold.json`. Its two discharges:

- `bostLowerBound` → `bostLowerBound_of_printed {n}.bostLowerBoundPrinted {t}.uniformizationLeafAll {t}.mumfordTorsionAlgClosed`;
- `gaudronRemondThm14` → `gaudronRemondThm14_of_printed {n}.gaudronRemondThm14Printed {t}.uniformizationLeafAll {t}.mumfordTorsionAlgClosed`.

Both new leaves are kind `published`. Bost's has the flag "locator UNVERIFIED (see the source)". GR's flag is
empty, so it gets the default "unread" flag. The dry run exits 0 with "strict count: 34/11 on 45 -> 34/11 on
45; strictest 34/11 -> 34/11". The dry-run module, `scratch/height-dict/FoldDryRun.lean` (the output without
its first line), compiles, and `HDec.HSyn.sixContactMin_of_open36` has standard axioms.

An optional spec, `scratch/height-dict/autofold-all4.json`, also replaces `javanpeykarBound` and
`pazukiCor13Upper`. Its dry run is the same (exit 0, 34/11 → 34/11), and `FoldDryRunAll4.lean` compiles with
standard axioms. Use it if the 11-16 dictionary rating applies to those two rows as well.

## 4. The dictionary steps

| step | before | now |
| --- | --- | --- |
| D1. `ℂ^g/Λ ≃ A_τ(ℂ)` is a homeomorphism and a group iso, and `A_τ(ℂ)` is a compact topological group | docstring, STANDARD | **proved** (`IsUnif.torusHomeo`, `isTopologicalGroup`; Hausdorff by the kernel's proved `analyticPointsT2`) |
| D2. `Φ` biholomorphic onto `A^an` | docstring, STANDARD | **not needed**: the printed definition never mentions `Φ`. The proof uses only `C¹`-regularity of `F ∘ Φ`, which is **proved** (`Holomorphic.hasStrictFDerivAt`) |
| D3. `(i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄ = |c|² covol(Λ)`, where `c` is the coefficient of `Φ*η` | docstring | **proved** (`volume_eq_of_normalized`, `isFaltingsMetricSq_of_metrized`), with existence (`exists_isNormalizedBy`) and uniqueness (`isFaltingsMetricSq_iff`) |
| D4. The height of the Néron model is the model height of a metrization, and `g = dim A` | kernel glue | proved from T35 in the kernel (`groupModel_height_eq`, `analyticUniformizationUnique_of_t35`, `uniformizationDim_of_t35`, `neronMetrizable_of_t35`) |
| D5. `ω_𝒢 = Γ(S, e*Ω¹_{𝒢/S})` (EGA IV 17.2.5) | docstring, UNVERIFIED | **proved at the stalks**: `omegaAt_map`, `theta_injective`, `omega_map`, `printedOmega_eq` (Mathlib's `kerCotangentToTensor`, exact sequence and section criterion) |

Definition-level readings that remain. Each is how the print's object is written with Mathlib's objects;
none is a theorem step.

| reading | why it is a reading, not a step |
| --- | --- |
| R1. The stalk of `Ω_{𝒩/S}` at `e(s)` is `Ω[𝒪_{𝒩,e(s)}/𝓞_L]`, and global sections of the lattice `e*Ω¹` are the intersection of its stalks in the generic fibre | Mathlib 4.35 has no sheaf of relative differentials on schemes, so the sheaf exists in Lean only through its stalks. Both facts are STANDARD: Kähler differentials commute with localization (Stacks 00RT, number UNVERIFIED), and a locally free sheaf on an integral scheme is the intersection of its stalks |
| R2. `A_τ(ℂ)` with its analytic topology is `(𝒢(ℂ)_τ, anTop)` | the kernel's convention: on an affine open, the topology of `U(ℂ) ⊂ ℂ^n` given by generators. Already used by the kernel's (proved) `analyticPointsT2` |
| R3. `(i/2)^g ∫_{A(ℂ)} η ∧ η̄` for the invariant `g`-form `η` is the total mass of the left-invariant measure whose density at `1` in algebraic coordinates is `|τ(l)|²` | the definition of the integral of a smooth density in charts, together with the invariance of `η`. Proved non-vacuous and single-valued |

## 5. Leaves and ratings

| leaf | source | rating |
| --- | --- | --- |
| `ZInQ.HeightDict.BostLowerBoundPrinted` (new; replaces `bostLowerBound`) | Bost, Sém. Bourbaki 795 (1994/95), Astérisque 237 (1996); display UNVERIFIED (as in height-split) | **printed form.** It is the old leaf with `IsStableFaltingsHeight` replaced by `IsPrintedStableHeight`, a definition built as the print builds it (§2; readings R1-R3). The normalization caveat is unchanged: the leaf uses Deligne's `h_D = h_F + (g/2) log π`, and there is a residual risk if Bost printed in `(i/4π)^g`. Locator UNVERIFIED |
| `ZInQ.HeightDict.GaudronRemondThm14Printed` (new; replaces `gaudronRemondThm14`) | Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4, p. 2060; `κ` on p. 2058 (read by the locator audit) | **printed form**, over the printed stable height in Faltings' original normalization `(i/2)^g`, which is the normalization of `IsFaltingsMetricSq` (readings R1-R3) |

No glue Prop is added, since the dictionary is proved. `uniformizationLeafAll` and `mumfordTorsionAlgClosed`
are existing textbook fields; the fold only reads them. A reviewer could still count R3 as a step. If so, the
precise Prop to state would be "the integral of the invariant form over the analytic manifold
`A^an` (sga1-etale's atlas) is the invariant measure normalized at `1`". That is a chart-by-chart restatement
of the same measure.

Proposed `docs/research/locators.md` rows (not added; locators.md is a shared note):

- `BostLowerBoundPrinted`: Bost, Astérisque 237 (1996), Exp. 795, the lower bound for `h_F`, in the same row
  as `bostLowerBound` (display UNVERIFIED).
- `GaudronRemondThm14Printed`: Gaudron–Rémond 2014, Thm 1.4 p. 2060, as for `gaudronRemondThm14`.

The optional rows `JavanpeykarBoundPrinted` (Javanpeykar 2014 Thm 1.1.1) and `PazukiCor13UpperPrinted`
(Pazuki 2012 Cor. 1.3(2), upper half; the level-2 coordinate risk is unchanged) are rated printed form for the
same reason: verbatim restatements over the printed height.

Note: `claims.tsv` shows `gaudronRemondThm14` held by gr14-narrow (forward direction only). The two pieces
of work compose: gr14-narrow's narrower statement can be restated over `IsPrintedStableHeight` in the same
way, using `isPrintedStableHeight_of`.

## 6. How much the vendored machinery gives

- **Kernel and height-glue (in this base).** Used throughout:
  - the analytic topology `anTop` and its Hausdorffness (`analyticPointsT2`, proved);
  - continuity of analytic uniformizations and the torus-homeomorphism pattern (`exists_linear_factor`);
  - from T35: uniqueness of uniformizations, `UniformizationDim`, `NeronMetrizable`;
  - T35 itself from `uniformizationLeafAll` and `mumfordTorsionAlgClosed` (`h38`);
  - `HeightBC.OmegaBC`'s stalk lemmas (`hom_unitSection`, `unitSection_stalkMapAt_hom`, `spec_mem_of_ker`,
    `stalkMapAt_germ'`) and `Metrization.germAlong_eventuallyEq`.
- **The vendored uniformization** (`BPAnalytic.Uniformization`, unif-printed's `MumfordComplexTorus`). It enters
  only through T35, for D4. The printed definition does not use it.
- **unif-topology / sga1-etale (wip/sga1-etale aa37ef8a).** These build `X(ℂ)` as an analytic manifold from
  SGA 1 XII 3.1. They are **not needed**: the printed metric is a measure on the topological group `A_τ(ℂ)`,
  normalized only at the identity in algebraic coordinates, so no chart atlas, manifold structure or
  integration of forms over charts is required. If a reviewer wants the integral over the manifold `A^an`
  literally (R3), sga1-etale's atlas is the one to use. `volume_eq_of_normalized` then applies unchanged once
  the chart-wise measure is shown to be left-invariant.
- **Mathlib 4.35 gaps filled here:**
  - holomorphic ⇒ strictly differentiable in several variables (`Holomorphic.lean`);
  - the volume of a uniformized compact group (`TorusVolume.lean`);
  - the conormal–Kähler comparison at stalks of a group scheme (`Conormal.lean`).

## 7. Files

- `ZInQKernel/Contrib/OneProof/HeightDictionary.lean` and `ZInQKernel/Contrib/OneProof/HeightDictionary/`
  (`TorusVolume.lean`, `Holomorphic.lean`, `Conormal.lean`). All are new.
- `scratch/height-dict/`:
  - `log.md`;
  - `Statements.md` (verbatim copies of `BostLowerBound`, `GaudronRemondThm14`, `IsStableFaltingsHeight`,
    `GroupModel.height`);
  - `DischargesCheck.lean`, `discharges.txt`;
  - `autofold.json`, `autofold-dryrun.txt`, `FoldDryRun.lean`;
  - optional: `autofold-all4.json`, `autofold-all4-dryrun.txt`, `FoldDryRunAll4.lean`;
  - `Conormal1.lean` (the development copy of `Conormal.lean`).
