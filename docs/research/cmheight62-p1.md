# cmheight62-p1: the exact height formula for every smooth model, and cmHeight62 from one finite-place Prop

**Status (first lines).** Both targets are proved, without `sorry` and with no new axioms:

* **Step 6, the exact formula, for every smooth model (no properness):**
  `ZInQ.Contrib.CMHeight62.finrank_mul_modelHeight_eq_exact'`
  (`ZInQKernel/Contrib/OneProof/CMHeight62/Final.lean`):

  ```
  ∀ {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    {E : PkgI3.AbVar K} (hdim : E.dim = 1) (D : ShortData E)
    (M : ZInQ.DefFaltings.MetrizedModel E L 1) (τ : (L →+* ℂ) → ℂ),
    (∀ σ, 0 < (τ σ).im ∧ HDec.CMBranch.IsPeriodAt E (σ.comp (algebraMap K L)) (τ σ)) →
    ∃ (hη : D.etaW M.model ≠ 0),
      ↑(Module.finrank ℚ L) * M.hodge.modelHeight =
        ∑ σ, CMBranch.summand62 (τ σ) +
          1 / 12 * (Real.log |↑(Algebra.norm ℚ (algebraMap K L D.W.Δ))| -
            12 * Real.log ↑(FractionalIdeal.absNorm
              (ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal.coefficientFractionalIdeal M.model hdim
                (D.etaW M.model) hη)))
  ```
  `#print axioms`: `[propext, Classical.choice, Quot.sound]`.

* **CMHeight62 from step 7:** `ZInQ.Contrib.CMHeight62.cmHeight62_of_step7' : Step7 → HDec.CMBranch.CMHeight62`
  (same file). `#print axioms`: `[propext, Classical.choice, Quot.sound]`.

* **The step-7 Prop, verbatim** (`ZInQKernel/Contrib/OneProof/CMHeight62/Assembly.lean`, `#print`ed):

  ```
  def ZInQ.Contrib.CMHeight62.Step7 : Prop :=
  ∀ (K : Type) [inst : Field K] [NumberField K] (L : Type) [inst_2 : Field L] [inst_3 : NumberField L]
    [inst_4 : Algebra K L] (E : PkgI3.AbVar K) (hdim : E.dim = 1) (D : ShortData E) (𝒢 : ZInQ.DefFaltings.GroupModel E L),
    AlgebraicGeometry.IsProper 𝒢.G.hom →
      ∀ (hη : D.etaW 𝒢 ≠ 0),
        |(Algebra.norm ℚ) ((algebraMap K L) D.W.Δ)| ≤
          FractionalIdeal.absNorm
              (ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal.coefficientFractionalIdeal 𝒢 hdim (D.etaW 𝒢) hη) ^ 12
  ```

* **Unproved sub-steps of steps 0-6: none.** The archimedean identity (steps 1, 2 and 4) is the
  theorem `archIdentity : ArchIdentity` (no hypotheses). Step 7 is the only open content.

* **No count change.** This task retires no frozen field: `Step7` together with the proved steps implies
  `CMHeight62`, not conversely, so the fold rule does not allow `Step7` to replace the field. Additive code only;
  nothing is folded; no existing file changed.

Base: `96f3a26b70770167ba4e9005a601a737dc618133`.

## 1. Files (all new)

`ZInQKernel/Contrib/OneProof/CMHeight62/`:

| file | content |
|---|---|
| `Archimedean.lean` | step 3 (`finrank_mul_modelHeight_eq`) and steps 5-6 in abstract form (`finrank_mul_modelHeight_eq_summand62`), over an arbitrary `MetrizedModel E L 1` |
| `Model.lean` | step 0: `exists_metrizedModel` |
| `Discriminant.lean` | `weierstrassCurve_ofTau_Δ : (PeriodPair.ofTau τ).weierstrassCurve.Δ = discAn τ` |
| `ShortModel.lean` | `ShortData`, `shortData`, `W`, `tE` (germ of `−x/y`), `bcProj`, `bcProj_identity`, `tL`, `tG`, `etaW` |
| `BcPt.lean` | `ptL : E_L(ℂ)_σ ≃* E(ℂ)_{σ∣K}`, evaluation compatibility, `isUniformization_ptL` |
| `Periods.lean` | step 1: `period_comparison` |
| `Eval.lean` | `ev` (value of a section at `Spec ℂ → X`), composition/restriction/ring lemmas |
| `Germ.lean` | the evaluation bridge `germAlong_mul_y` |
| `Short.lean` | `short_comparison` (`x = u²℘`, `y = u³℘'/2`), `sigma_W_Δ : σ(Δ_W) = u¹² discAn τ` |
| `Analysis.lean` | Laurent analysis of `−2℘/℘'` at `0`; `hasDerivAt_of_eventually_ψ` |
| `Covolume.lean` | `covolume_eq_of_mem_iff : covol(a(ℤ+τℤ)) = ‖a‖² Im τ` |
| `Assembly.lean` | `ArchIdentity`, `Step7`, `finrank_mul_modelHeight_eq_exact`, `cmHeight62_of_step7` |
| `Final.lean` | `arch_at`, `archIdentity`, `finrank_mul_modelHeight_eq_exact'`, `cmHeight62_of_step7'` |

`lake build ZInQKernel.Contrib.OneProof.CMHeight62.Final`: `Build completed successfully` (VERIFIED). The results log
is `scratch/cmheight62-p1/log.md`; the axiom audit is `scratch/cmheight62-p1/Axioms.lean`.

## 2. The route as built (VERIFIED: compiled)

* **Step 0.** `exists_metrizedModel hdim 𝒢 : ∃ M : MetrizedModel E L 1, M.model = 𝒢`, from
  `ZInQ.HeightGlue.metrizationOfUniformization`, T35 moved along `θ`
  (`ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists`) and the tree's T35
  `HDec.CMBranch.CMjBridges.uniformization_exists`. Audit of the T35 pieces used (they had not been audited):
  `uniformization_exists` and `analyticUniformizationOfDim_of_uniformizationExists` both depend on
  `[propext, Classical.choice, Quot.sound]`.
* **Step 1.** `period_comparison`: T35 for `E_L` at `σ` → `θ` → compared with the model's uniformization by
  `analyticUniformizationUnique_of_t35` (never assumed) → pushed to `E` by `ptL` (= `AbVarBC.bcPt`, `Ω = ℂ`) →
  compared with the `IsPeriodAt` uniformization by `HomLinearLift` with `f = id`
  (`homLinearLift_of_corr (AvSplit.Final.h69 uniformizationLeafAll_proof gagaMorphism_proof)`). Output: `k ≠ 0` with
  `ptL (χ (Φ z)) = Φ_E (k z)`, `Λ_σ = {z : k z ∈ Λ_E}`, and openness of `{z | χ(Φ z) ∈ W}`. Only the
  model → generic-fibre direction through `χ`, `θ` is used, never the direction from `M.arch` to `E`.
* **Step 2.** The short model is the one of `abVar_shortSections_of_genusOne`, with the proved genus-one input
  `abVarFunctionFieldGenusOne` (JDescent4Genus). `−x/y` has order `1` at the identity place (`ord_fXY`), so by
  `hp` it is the image of a germ `tE ∈ 𝔪_{E,0}`; `tL` is its image under the stalk map of `E_L → E` (which fixes
  the identity, `bcProj_identity`); `tG = originStalkEquiv⁻¹ tL ∈ 𝔪_ξ`; `η_W = 𝒢.wedge ![tG]`. `η_W ≠ 0` is proved
  from step 4 (`coeff_σ η_W ≠ 0`). `Jη = coefficientFractionalIdeal 𝒢 hdim η_W _` = `{a : a • η_W ∈ ⋀¹ω_𝒢}`, so
  `⋀¹ω_𝒢 = Jη · η_W` (the colon-ideal reading).
* **Step 3.** `finrank_mul_modelHeight_eq`: `d·h(M) = −log N(Jη) − Σ_σ log‖η‖_σ` for every `M` and every
  `η ≠ 0` (through a nonzero `a ∈ Jη`, `secIndex_detLattice_eq_norm_div` and the product formula).
* **Step 4.** `sigma_W_Δ` (`σ|_K(Δ_W) = u¹² Δ(ℤτ+ℤ)`, from the short comparison: the JDescent `W.map σ`
  computation redone as a lemma), `weierstrassCurve_ofTau_Δ` (`Δ(ℤτ+ℤ) = (64π¹²/27)(E₄³−E₆²) = (2π)¹²η²⁴`),
  and the coefficient: `germAlong_mul_y` (the evaluation bridge: the germ equality is moved through the generic
  fibre `𝒢_L` with `originStalkEquiv_spec`, points through `gpt p = secC ≫ mapG p`, and `r · y = −x` on
  `V ∩ (E∖0)` by injectivity into the function field) gives `t(Φ(w)) = −2℘(aw)/(u℘'(aw))` near `0` with
  `a = k/c`, and `hasDerivAt_of_eventually_ψ` (`℘ = w⁻² + O(1)`, `℘' = −2w⁻³ + O(1)`) gives
  `coeff_σ η_W = jacDet = a/u`. With `covol Λ_σ = ‖c/k‖² Im τ`: `‖η_W‖_σ² = Im τ / |u|²` and
  `|σΔ_W| · ‖η_W‖_σ¹² = |discAn τ| (Im τ)⁶` (`arch_at`).
* **Step 5.** `sum_log_norm_eq` (`HodgeData.sum_log_norm_embeddings`).
* **Steps 6-7.** `finrank_mul_modelHeight_eq_exact'`; `cmHeight62_of_step7'`: take `D = shortData E`, `M` from step
  0, the formula, and `log |N Δ_W| ≤ 12 log N(Jη)` from `Step7` (`N Δ_W ≠ 0`); then
  `stableFaltingsHeight_le`.

Neither properness, CM, a reduced period, an existential model, `hNeron` nor `PeriodAreaFormula` is used anywhere;
properness enters only through the hypothesis of `Step7`.

## 3. `#discharges`

`scratch/cmheight62-p1/Discharges.lean` (imports `ZInQKernel.OneProof.Main`, `ZInQKernel.OneProof.Discharges`,
`ZInQKernel.Contrib.OneProof.CMHeight62.Final`), run with `lake env lean` after `lake build ZInQKernel.OneProof.Main
ZInQKernel.OneProof.Discharges` (Build completed successfully). The lines for the new theorems (VERIFIED):

```
DISCHARGES [OpenResearchLeaves79.cmHeight62] by ZInQ.Contrib.CMHeight62.cmHeight62_of_step7
  still assumes: [ZInQ.Contrib.CMHeight62.ArchIdentity, ZInQ.Contrib.CMHeight62.Step7]
DISCHARGES [OpenResearchLeaves79.cmHeight62] by ZInQ.Contrib.CMHeight62.cmHeight62_of_step7'
  still assumes: [ZInQ.Contrib.CMHeight62.Step7]
#discharges: 21 open hypotheses, 20769 theorems checked, 369 discharge one
```

(The other `cmHeight62` lines of the run are the pre-existing bundle projections `CMInputs2.cmHeight62`,
`OpenResearchLeaves6xNOS/DS.cmHeight62`, … .) So `cmHeight62` is matched with the single remaining assumption
`Step7`; per the fold rule this is not a discharge (no count change).

## 4. Gap analysis for step 7 (no Lean)

**The smallest faithful local statement.** Let `R` be a DVR with fraction field `F` and valuation `v`, `𝒢/R` a
proper smooth group scheme with generic fibre an elliptic curve `E/F`, `W` a Weierstrass equation of `E` over
`F` (not necessarily integral) with differential `ω_W = d(−x/y)` at the origin, and `s = μ·ω_W` a generator
of the free rank-one `R`-module `e*Ω¹_{𝒢/R}`. Then `v(Δ_W) ≤ 12 v(μ)` (with equality, since `𝒢` is then the Néron
model and `W` changes to a minimal model with unit discriminant; STANDARD: Silverman, AEC VII.1 and the
invariance `Δ_{W'} = u⁻¹² Δ_W`, `ω_{W'} = u ω_W`; theorem numbers UNVERIFIED). Globally over `𝓞_L` this is
`|N_{L/ℚ}(Δ_W)| ≤ N(Jη)¹²` because `ω_𝒢 = Jη · η_W` and `v_𝔭(Jη) = v_𝔭(μ_𝔭)` at each prime `𝔭`.

Proof sketch (STANDARD): over `R` with `𝒢` proper smooth, `E` has good reduction, so it has an integral
minimal Weierstrass model `W₀` with `Δ_{W₀} ∈ R^×`. The Weierstrass scheme `𝒲₀ ⊂ ℙ²_R` is proper smooth with
generic fibre `E`, so `𝒲₀ ≅ 𝒢` (both are Néron models; or `NeronGoodModelIso` applied to an extension
`𝒲₀ → 𝒢`), and `ω_{W₀}` generates `e*Ω¹_{𝒲₀/R}` (at the origin of the special fibre it is the invariant
differential of a smooth cubic). If `W` is obtained from `W₀` by `(u, r, s, t)`, then `Δ_W = u⁻¹² Δ_{W₀}` and
`ω_W = u ω_{W₀}` (AEC III.1, UNVERIFIED numbers), so `s = ω_{W₀} = u⁻¹ ω_W`, `μ = u⁻¹`, and
`v(Δ_W) = −12 v(u) = 12 v(μ)`: equality. (`d(−x/y)` and the invariant differential `dx/(2y + a₁x + a₃)` have the
same value at the origin, since `−x/y` is a uniformizer with `dx/(2y) = (1 + O(z)) dz`.)

**What the tree already has (VERIFIED: read).**

* Néron existence over a Dedekind base: the leaves `NeronSchemeExtensionDVR`, `NeronSchemeExtensionDedekind`
  (`ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean:56,66`; they are hypotheses there, not theorems).
* `neronGoodModelIso_of_dvr : NeronSchemeExtensionDVR → NeronGoodModelIso` and `neronGoodModelIso_of_dedekind`
  (`ZInQKernel/Contrib/OneProof/NeronGoodModelIso.lean:541,606`); `NeronGoodModelIso`
  (`MumfordGroupLawNeron.lean:99`): over a DVR, a morphism `ψ : F → N` from a proper smooth geometrically
  connected `F` with abelian-variety fibres to a smooth separated `N` that is an isomorphism on generic fibres is
  an isomorphism.
* Zariski connectedness and NOS (a)⇒(b) (memory of earlier tasks; not re-read in this run: UNVERIFIED here).
* On the archimedean side, all of the present task (§2). On the lattice side: `coefficientFractionalIdeal`,
  `omegaCoefficientEquiv` (`ω_𝒢 ≃ Jη`), `secIndex_detLattice_eq_norm_div` (HodgeLatticeIdeal), and
  `omegaLocalization`/`OmegaBaseChange` (`ZInQKernel/Contrib/HeightBC/OmegaBC.lean:603-635`), the conormal
  description `ZInQ.HeightDict.Conormal.omega_map` (`HeightDictionary/Conormal.lean`).

**What is missing (each with the declarations it would connect).**

1. *The Weierstrass side over a DVR.* A Weierstrass scheme `𝒲(W₀) ⊂ ℙ²_R` for an integral `W₀` with
   `Δ ∈ R^×`, as an `Over (Spec R)` that is proper, smooth, with a `GrpObj` structure (or at least a section
   `e`) and `IsAbVarFibre` fibres, plus the computation that `ω_{W₀}` is a generator of `e*Ω¹_{𝒲/R}`.
   Connects: `NeronGoodModelIso` (input `F := 𝒲(W₀)`), `GroupModelO` (`ZInQKernel/OneProof/H/TailZ7.lean:161`), and
   the tree's projective Weierstrass objects over fields (`ZInQ.Contrib.RC53Assist.HodgeLineBinding`:
   `Proj E'.toProjective.grading`, `paramZ`, `originParameter`, `hodgeEval_invariantDifferential`), which exist
   only over a field. Alternative: Riemann–Roch with base change on `𝒢_R` (the sections `1, x, y` of
   `𝒪(2e), 𝒪(3e)` spread out over `R`), which the tree does not have either.
2. *AV7 if `NeronGoodModelIso` is fed the Weierstrass scheme:* the `AbVar` structure (group law, properness,
   geometric integrality) on the generic fibre of `𝒲(W₀)`, needed for the `IsAbVarFibre` hypothesis.
3. *Existence of a minimal (unit-discriminant) integral model* `W₀` of `E` over `R` when `E` has good reduction
   (from `𝒢` proper smooth): `v(Δ_min) = 0`. Standard (Tate's algorithm / AEC VII.5.1), not in the tree. Connects
   `ShortData.W` (over `K`) with an `R`-integral change of variables `(u, r, s, t)`.
4. *DVR-to-`𝓞_L` comparison for `ω`.* `GroupModelO` has no `omega` API. Needed: for `𝔭 ∈ Spec 𝓞_L`, the
   localization `(ω_𝒢)_𝔭 = ω_{𝒢_{𝓞_{L,𝔭}}}` (a `GroupModelO` over the valuation ring of `𝔭`), and the local
   index `v_𝔭(Jη) = v_𝔭(μ_𝔭)`. Nearest pieces: `ZInQ.HeightBC.omegaLocalization` (`OmegaBC.lean:635`, for
   `GroupModel` over `𝓞_L`), `GroupModel.omegaAt`, `HeightDictionary/Conormal.lean` (`omegaAt_map`). Connects
   `coefficientFractionalIdeal` with `GroupModelO` base change along `𝓞_L → 𝓞_{L,𝔭}`.
5. *The identification of `η_W` through base change of the Weierstrass equation:* `D.etaW` is defined from
   `−x/y ∈ K(E)`; the DVR statement needs it compared with `ω_{W₀}` on `𝒲(W₀)` after `K → L → L_𝔭`
   (`(u,r,s,t)` acting on `−x/y`). This is field-level algebra once item 1 exists.
6. *Assembly:* `|N_{L/ℚ} Δ_W| = Π_𝔭 N𝔭^{v_𝔭(Δ_W)}` and `N(Jη) = Π_𝔭 N𝔭^{v_𝔭(Jη)}`
   (`FractionalIdeal.absNorm` of a product of prime powers), then items 1-5 prime by prime.

Items 1 and 3 are the substantial ones; 2 is AV7 (known open); 4-6 are glue of medium size.
