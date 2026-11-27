import ZInQKernel.Contrib.OneProof.CMHeight62.BcPt
import ZInQKernel.Contrib.OneProof.CMHeight62.Model

/-! # cmheight62-p1, step 1: the period lattice of a metrized model versus a period of `E`

For a metrized model `M` of `E_L` (`E/K` an elliptic curve), its uniformization `Φ` at
`σ : L → ℂ` and any uniformization `Φ_E` of `E` at `σ|_K`, there is `k ≠ 0` with
`ptL (χ (Φ z)) = Φ_E (k z)` and `Λ_σ = k⁻¹ Λ_E`.

Route (as prescribed): T35 for `E_L` at `σ` (`uniformization_exists`), pushed to the model by
`θ` (`ZInQ.Metrization2.theta`), compared with `Φ` by `AnalyticUniformizationUnique`
(`analyticUniformizationUnique_of_t35`), and pushed to `E` by `ptL` (`AbVarBC.bcPt`), compared
with `Φ_E` by `HomLinearLift` with `f = id` (`AvSplit.Final.h69`). -/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
open _root_.ZInQ.LeafPush2 (CPts cptObj cDom cEvalAt IsUniformization)

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- `θ ∘ Φ_L` is an analytic uniformization of the model (the proof of
`analyticUniformizationOfDim_of_uniformizationExists`, for a given `Φ_L`). -/
theorem isAnalyticUniformization_theta (𝒢 : GroupModel E L) (σ : L →+* ℂ) {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ₀ : (Fin g → ℂ) → CPts (E.baseChange L) σ}
    (h : IsUniformization σ Λ Φ₀) :
    𝒢.IsAnalyticUniformization σ Λ (fun z => ZInQ.Metrization2.theta 𝒢 (Φ₀ z)) := by
  obtain ⟨hmul, hker, hsurj, hopen, hdiff⟩ := h
  refine ⟨fun z w => ?_, fun z => ?_, ?_, fun U => ?_, fun U s => ?_⟩
  · simp only [hmul, ZInQ.Metrization2.theta_mul]
  · rw [← hker z, ← ZInQ.Metrization2.theta_one 𝒢 (τ := σ)]
    exact (ZInQ.Metrization2.theta_injective 𝒢).eq_iff
  · exact (ZInQ.Metrization2.theta_surjective 𝒢).comp hsurj
  · exact hopen ((ZInQ.Metrization2.toModel 𝒢) ⁻¹ᵁ U)
  · have := hdiff ((ZInQ.Metrization2.toModel 𝒢) ⁻¹ᵁ U) ((ZInQ.Metrization2.toModel 𝒢).app U s)
    refine this.congr fun z _ => ?_
    exact (ZInQ.Metrization2.evalAt_theta 𝒢) (Φ₀ z) U s

/-- `HomLinearLift`, proved in the tree. -/
theorem homLinearLift : ZInQ.HomUnify.HomLinearLift :=
  ZInQ.HomUnify.homLinearLift_of_corr (AvSplit.Final.h69
    uniformizationLeafAll_proof
    ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof)

theorem eq_smul_one (z : Fin 1 → ℂ) : z = z 0 • (fun _ => (1 : ℂ)) := by
  funext i; fin_cases i; simp

/-- A discrete subgroup of `ℂ¹` is not everything. -/
theorem not_forall_mem_of_discrete (Λ : Submodule ℤ (Fin 1 → ℂ)) [DiscreteTopology Λ] :
    ¬ ∀ z, z ∈ Λ := by
  intro hall
  have hd : IsDiscrete (Λ : Set (Fin 1 → ℂ)) := isDiscrete_iff_discreteTopology.mpr ‹_›
  obtain ⟨ε, hε, hball⟩ := Metric.exists_ball_inter_eq_singleton_of_mem_discrete hd Λ.zero_mem
  let w : Fin 1 → ℂ := fun _ => ((ε / 2 : ℝ) : ℂ)
  have hw : w ∈ Metric.ball (0 : Fin 1 → ℂ) ε ∩ (Λ : Set _) := by
    refine ⟨?_, hall w⟩
    rw [Metric.mem_ball, dist_zero_right, pi_norm_const]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  rw [hball] at hw
  have := congrFun (Set.mem_singleton_iff.mp hw) 0
  simp only [w, Pi.zero_apply, Complex.ofReal_eq_zero] at this
  linarith

/-- **Step 1: period comparison.** -/
theorem period_comparison [NumberField K] (hdim : E.dim = 1) (M : MetrizedModel E L 1)
    (σ : L →+* ℂ) {Φ : (Fin 1 → ℂ) → M.model.Pts σ}
    (hΦ : M.model.IsAnalyticUniformization σ (M.hodge.periods σ) Φ)
    {ΛE : Submodule ℤ (Fin 1 → ℂ)} {ΦE : (Fin 1 → ℂ) → CPts E (σ.comp (algebraMap K L))}
    (hE : IsUniformization (σ.comp (algebraMap K L)) ΛE ΦE) :
    ∃ k : ℂ, k ≠ 0 ∧ (∀ z, ptL E σ (ZInQ.Metrization2.chi M.model (Φ z)) = ΦE (k • z)) ∧
      (∀ z, z ∈ M.hodge.periods σ ↔ k • z ∈ ΛE) ∧
      (∀ W : (E.baseChange L).X.left.Opens,
        IsOpen {z | ⊤ ≤ (ZInQ.Metrization2.chi M.model (Φ z)).left ⁻¹ᵁ W}) := by
  have hg : E.dim = ((1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  have hgL : (E.baseChange L).dim = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [← hg]; exact G0Dim.dim_baseChange L E.X.left E.X.hom
  obtain ⟨ΛL, Φ₀, hdL, hZL, hU⟩ :=
    HDec.CMBranch.CMjBridges.uniformization_exists L (E.baseChange L) σ 1 hgL
  have hG := isAnalyticUniformization_theta M.model σ hU
  obtain ⟨T, hT, hTΛ⟩ := ZInQ.HeightGlue.analyticUniformizationUnique_of_t35
    HDec.CMBranch.CMjBridges.uniformization_exists K E L M.model σ 1 ΛL (M.hodge.periods σ)
    (fun z => ZInQ.Metrization2.theta M.model (Φ₀ z)) Φ hG hΦ
  have hchi : ∀ z, ZInQ.Metrization2.chi M.model (Φ z) = Φ₀ (T z) := by
    intro z; rw [hT z, ZInQ.Metrization2.chi_theta]
  have hE' := isUniformization_ptL E σ hU
  obtain ⟨Mlin, hM⟩ := homLinearLift K E E (σ.comp (algebraMap K L)) 1 1 ΛL ΛE
    (fun z => ptL E σ (Φ₀ z)) ΦE hg hg hE' hE (PkgI3.AbVar.Hom.mk' (𝟙 E.X))
  simp only [PkgI3.AbVar.Hom.hom_mk', Category.comp_id] at hM
  set k : ℂ := Mlin (T (fun _ => 1)) 0 with hk
  have hlin : ∀ z, Mlin (T z) = k • z := by
    intro z
    conv_lhs => rw [eq_smul_one z, map_smul, map_smul]
    funext i; fin_cases i
    simp [hk, mul_comm]
  have hpt : ∀ z, ptL E σ (ZInQ.Metrization2.chi M.model (Φ z)) = ΦE (k • z) := by
    intro z; rw [hchi, ← hlin, hM]
  have hlat : ∀ z, z ∈ M.hodge.periods σ ↔ k • z ∈ ΛE := by
    intro z
    rw [hTΛ z, ← hU.2.1, ← hE.2.1, ← hlin, hM, MulEquiv.map_eq_one_iff]
  have hop : ∀ W : (E.baseChange L).X.left.Opens,
      IsOpen {z | ⊤ ≤ (ZInQ.Metrization2.chi M.model (Φ z)).left ⁻¹ᵁ W} := by
    intro W
    have hset : {z | ⊤ ≤ (ZInQ.Metrization2.chi M.model (Φ z)).left ⁻¹ᵁ W} =
        (fun z => T z) ⁻¹' cDom Φ₀ W := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      rw [hchi]
      rfl
    rw [hset]
    exact (hU.2.2.2.1 W).preimage
      (LinearMap.continuous_of_finiteDimensional (T : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)))
  refine ⟨k, ?_, hpt, hlat, hop⟩
  intro hk0
  rw [hk0] at hlat
  have := M.hodge.periods_discrete σ
  exact not_forall_mem_of_discrete _ fun z => (hlat z).mpr (by rw [zero_smul]; exact ΛE.zero_mem)

end ZInQ.Contrib.CMHeight62
