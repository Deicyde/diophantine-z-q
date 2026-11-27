# cmheight62-p1 results log

Base: 96f3a26b70770167ba4e9005a601a737dc618133 (confirmed `git rev-parse HEAD`).

## Order-of-work 1: builds
- `lake build ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.All ZInQKernel.Contrib.RC53Assist.HodgeLatticeIdeal.All`:
  Build completed successfully (10688 jobs), 4m58s. Only module-system import warnings. VERIFIED.
- Probe: CMHeight62 is stated over `_root_.ZInQ.DefFaltings.{GroupModel, stableFaltingsHeight}` (same types as
  HodgeLatticeIdeal); `IsPeriodAt` uses `HDec.LeafAdopt.abVarEquiv`. VERIFIED (#print).

## Archimedean.lean (steps 3, 5, 6 abstract) — compiles (lake env lean, no errors). VERIFIED
- `exists_mem_coefficientFractionalIdeal_ne_zero`
- `finrank_mul_modelHeight_eq` (step 3): d·h(M) = −log N(Jη) − Σ_σ log ‖η‖_σ, any M : MetrizedModel E L 1, any η ≠ 0.
  Proof: a ∈ Jη nonzero, a•η ∈ lattice, degreeAt(a•η), secIndex_detLattice_eq_norm_div, product formula.
- `sum_log_norm_eq` (step 5): Σ log|σD| = log|N_{L/ℚ}D|.
- `finrank_mul_modelHeight_eq_summand62` (step 6 abstract): from per-σ hypothesis
  |σD|·‖η‖_σ^12 = |discAn τ_σ|·(Im τ_σ)^6, d·h = Σ summand62 + (1/12)(log|N D| − 12 log N Jη).

## Step 0 — Model.lean compiles. VERIFIED
- `exists_metrizedModel (hdim : E.dim = 1) (𝒢 : GroupModel E L) : ∃ M : MetrizedModel E L 1, M.model = 𝒢`
  from `ZInQ.HeightGlue.metrizationOfUniformization` + `ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists`
  + `HDec.CMBranch.CMjBridges.uniformization_exists` (T35, proved in tree).
- T35 audit (#print axioms, VERIFIED):
  'HDec.CMBranch.CMjBridges.uniformization_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
  'ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists' depends on axioms: [propext, Classical.choice, Quot.sound]
- `abVarFunctionFieldGenusOne` is proved (ZInQKernel/Contrib/OneProof/JDescent4Genus.lean:14), so the short model of
  JDescent5Sections is unconditional.
- NOTE: from 21:2x the sandbox hook blocks systemd-run; Lean runs continue as LEAN_NUM_THREADS=4 nice lake ... (one at a time).

## Step 4 (second bullet) — Discriminant.lean compiles. VERIFIED
- `weierstrassCurve_ofTau_Δ (τ : ℍ) : (PeriodPair.ofTau τ).weierstrassCurve.Δ = CMBranch.discAn τ`
  (vendored kw_discriminant_ofTau_eq + Mathlib discriminant_eq_E₄_cube_sub_E₆_sq + discriminant = η^24).

## Step 2 (definitions) — ShortModel.lean compiles. VERIFIED
- `ShortData A` (bundles abVar_shortSections_of_genusOne output), `shortData A hdim` (choice).
- `D.W := ⟨0,0,0,a,b⟩`, `W_Δ_ne_zero`, `fXY = −X/Y`, `ord_fXY = 1`, `tE` (germ in 𝒪_{E,0} with image −x/y),
  `tE_mem_maximalIdeal`, `bcProj`, `bcProj_identity` (projection E_L → E fixes identity), `tL`, `tG 𝒢 ∈ 𝔪_ξ`,
  `etaW 𝒢 := 𝒢.wedge ![tG 𝒢]`.

## Assembly.lean compiles. VERIFIED
- `ArchIdentity : Prop` (steps 1, 2-nonvanishing, 4): open sub-step at this point.
- `Step7 : Prop`.
- `finrank_mul_modelHeight_eq_exact (hA : ArchIdentity) ...` (step 6 exact formula, any smooth model).
- `cmHeight62_of_step7 (hA : ArchIdentity) (h7 : Step7) : HDec.CMBranch.CMHeight62`.
- Tree facts found (VERIFIED, read): JDescent2 `shortWeierstrassComparison_of_doublePole` +
  JDescent5 `abVar_period_abscissa_even`, `abVar_evaluatedPole_of_order`, `abVar_period_mem_punctured` give, for
  any IsPeriodAt-uniformization (Λ,Φ,s) of E at σ|K, u ≠ 0 with x(Φ(sz)) = u²℘(z), y(Φ(sz)) = u³℘'(z)/2 off the
  lattice (CM hypotheses of CMPeriodShortCoordinatesDoublePole unused in its proof).

## BcPt.lean compiles. VERIFIED
- `ptL E σ : CPts (E.baseChange L) σ ≃* CPts E (σ.comp (algebraMap K L))` (bcPt, Ω = ℂ), `ptL_left`,
  `cEvalAt_ptL`, `cDom_ptL`, `isUniformization_ptL`.

## Step 1 — Periods.lean compiles. VERIFIED
- `isAnalyticUniformization_theta`, `homLinearLift` (= homLinearLift_of_corr (h69 uniformizationLeafAll_proof gagaMorphism_proof)),
  `not_forall_mem_of_discrete`,
- `period_comparison hdim M σ hΦ hE : ∃ k ≠ 0, (∀ z, ptL E σ (chi M.model (Φ z)) = ΦE (k • z)) ∧ (∀ z, z ∈ M.hodge.periods σ ↔ k • z ∈ ΛE)`
  by T35 → theta → analyticUniformizationUnique_of_t35 → ptL → HomLinearLift(f = id).

## Eval.lean, Germ.lean compile (evaluation bridge). VERIFIED
- `ev q V s` (value at Spec ℂ → X), `ev_comp`, `ev_res`, `ev_mul`, `ev_neg`.
- `stalkCongr_germ`, `fstGF`, `genE := gen.hom.left ≫ bcProj`, `genE_unit`,
  `germ_pullbacks_eq` (germs at ξ_L of the pull-backs of reps of tG and tE agree; uses originStalkEquiv_spec).
- `ptc`, `top_le_preimage_iff`, `gpt p := secC ≫ mapG p`, `gpt_fst`, `chi_left`, `gpt_eq`, `evalAt_eq_ev`,
  `ptL_chi_left`, `cEvalAt_ptL_chi_eq_ev`, `one_left_apply`, `chi_one`, `gen_inv_identity`, `gpt_one_apply`.
- `rep_mul_y`: r|·y| = −x| on V ⊓ (E∖0) (germToFunctionField injectivity), `ev_rep_mul_y`.
- `germAlong_mul_y` (bridge): ∀ᶠ z in 𝓝 0, p z ∈ E∖0 → germAlong Φ tG z · y(p z) = −x(p z), p z = ptL (chi (Φ z)),
  given openness of {z | gpt (Φ z) ∈ W} for opens W of 𝒢_L.
- Pitfall: (cptObj σ).left vs (ptC σ).left vs Spec ℂ are only defeq; `rw` fails on morphisms between them —
  use term-mode Eq.trans/congrArg (TailE style).

## Step 4 (first bullet) — Short.lean compiles. VERIFIED
- `cEvalAt_sectionConst`, `short_comparison` (u ≠ 0, x(Φ_E(cw)) = u²℘(w), y = u³℘'(w)/2, Φ_E(cw) ∈ E∖0 off the lattice;
  JDescent2 proof re-run keeping D's x, y), `exists_weierstrassP_eq'`, `sigma_W_Δ : σ(Δ_W) = u^12 · discAn τ`.

## Step 4 (analysis) — Analysis.lean compiles. VERIFIED
- `wp_eq` (℘ = 1/w² + ℘[L-0]), `dwp_eq` (℘' = −2/w³ + ℘'[L-0]), `numψ`, `denψ`, `ψ`, `hasDerivAt_ψ` (ψ'(0) = 1/u),
  `ratio_eq_ψ`, `eventually_denψ_ne_zero`, `dwp_ne_zero`, `hasDerivAt_of_eventually_ψ`.

## Covolume.lean compiles. VERIFIED
- `covolume_eq_of_mem_iff : (∀ z, z ∈ Λ ↔ ∃ m n, z 0 = a(m+nτ)) → covol Λ = ‖a‖² Im τ`
  (BPAnalytic.covolume_periodLattice g = 1 + covolume_comap_mul_det).

## Final.lean compiles (lake build ...CMHeight62.Final: Build completed successfully). VERIFIED
- `arch_at`: coeff_σ η_W = (k/c)/u ≠ 0, covol Λ_σ = ‖c/k‖² Im τ, ‖η_W‖² = Im τ/‖u‖², identity.
- `archIdentity : ArchIdentity` (no hypotheses).
- `finrank_mul_modelHeight_eq_exact'` (step 6, unconditional), `cmHeight62_of_step7' : Step7 → HDec.CMBranch.CMHeight62`.
- #print axioms (scratch/cmheight62-p1/Axioms.lean): every listed theorem depends on [propext, Classical.choice, Quot.sound].
- grep: no sorry/axiom/admit in ZInQKernel/Contrib/OneProof/CMHeight62/.
- Pitfalls: `set` on M.model created shadowed Φ✝ and timeouts — write terms out / top-level helper defs (`fOf`);
  rw [top_le_preimage_iff] on (ptC σ).left morphisms timed out — use a dedicated lemma (`zero_mem_dom`).
- #discharges run: see scratch/cmheight62-p1/discharges.out (cmHeight62_of_step7' still assumes [Step7]). VERIFIED
