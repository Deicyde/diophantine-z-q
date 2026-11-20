import ZInQKernel.Contrib.OneProof.RC.X0Model3.Overlap
import ZInQKernel.Contrib.OneProof.RC.X0Model2.ModelOne

/-! The normalized branch comparison and the rational model at every nonzero
level (tex 2836–2844, 2915–2919; on the spot, provenance (c)). -/

noncomputable section

open AlgebraicGeometry Filter ModularCurve
open scoped Topology MatrixGroups
namespace ZInQ.Manuscript.RC.X0Model3

open X0Model2

/-- Equal valuative complex points on a common j-fiber have the same
punctured second-coordinate germ after an element of the center stabilizer. -/
theorem exists_stabilizer_germ_match (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    (γ₁ γ₂ : SL(2, ℤ)) (h : X0Model.complexPoint N (γ₁ • τ) = X0Model.complexPoint N (γ₂ • τ)) :
    ∃ s : SL(2, ℤ), s • τ = τ ∧
      (fun z : ℂ => X0Model.analyticJN N (γ₁ • UpperHalfPlane.ofComplex z))
        =ᶠ[𝓝[≠] (τ : ℂ)]
      (fun z : ℂ => X0Model.analyticJN N ((γ₂ * s) • UpperHalfPlane.ofComplex z)) := by
  obtain ⟨U, hU, hm⟩ := exists_nhds_germ_match_of_overlap N τ γ₁ γ₂
  apply hm
  let σ₁ := γ₁ • τ
  let σ₂ := γ₂ • τ
  obtain ⟨a, b, hr⟩ := exists_analyticJN_ratio N
  have hcoe : ((↑) : UpperHalfPlane → ℂ) '' U ∈ 𝓝 (τ : ℂ) := by
    rw [← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq]
    exact image_mem_map hU
  have hback : γ₂⁻¹ • σ₂ = τ := inv_smul_smul _ _
  have ht := slMoebius_tendsto γ₂⁻¹ σ₂
  rw [hback] at ht
  have hv := ht.eventually (mem_nhdsWithin_of_mem_nhds hcoe)
  let V : Set ℂ := {w | w ≠ (σ₂ : ℂ) →
    (finitePointEval N (UpperHalfPlane.ofComplex w) a =
      X0Model.analyticJN N (UpperHalfPlane.ofComplex w) *
        finitePointEval N (UpperHalfPlane.ofComplex w) b ∧
      finitePointEval N (UpperHalfPlane.ofComplex w) b ≠ 0) ∧
    slMoebius γ₂⁻¹ w ∈ ((↑) : UpperHalfPlane → ℂ) '' U} ∩ {w | 0 < w.im}
  have hV : V ∈ 𝓝 (σ₂ : ℂ) :=
    inter_mem (eventually_nhdsWithin_iff.mp ((hr σ₂).and hv))
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds σ₂.im_pos)
  have hov := (slMoebius_tendsto γ₁ τ).eventually
    ((eventually_overlap_of_complexPoint_eq N σ₁ σ₂ h V hV).and (hr σ₁))
  apply Eventually.frequently
  filter_upwards [hov, mem_nhdsWithin_of_mem_nhds
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with z hz hzH
  let z' : UpperHalfPlane := ⟨z, hzH⟩
  have hzγ : UpperHalfPlane.ofComplex (slMoebius γ₁ z) = γ₁ • z' := by
    rw [← show ((γ₁ • z' : UpperHalfPlane) : ℂ) = slMoebius γ₁ z from coe_sl_smul γ₁ z',
      UpperHalfPlane.ofComplex_apply]
  obtain ⟨⟨w, ⟨hw, hwH⟩, hwσ, hp⟩, ha, _⟩ := hz
  obtain ⟨⟨hc, hd⟩, v, hvU, hvw⟩ := hw hwσ
  let w' : UpperHalfPlane := ⟨w, hwH⟩
  have hγv : γ₂ • v = w' := by
    have he : v = γ₂⁻¹ • w' := UpperHalfPlane.coe_injective
      (hvw.trans (coe_sl_smul γ₂⁻¹ w').symm)
    rw [he, smul_inv_smul]
  have hw' : UpperHalfPlane.ofComplex w = w' := UpperHalfPlane.ofComplex_apply w'
  have hz' : UpperHalfPlane.ofComplex z = z' := UpperHalfPlane.ofComplex_apply z'
  rw [hzγ, hw'] at hp
  rw [hzγ] at ha
  rw [hw'] at hc hd
  have hab := finitePointEval_eq N (γ₁ • z') w' hp
  rw [hab, hc] at ha
  refine ⟨v, hvU, ?_, ?_⟩
  · rw [hz', ← analyticJ_smul γ₁ z', ← analyticJ_smul γ₂ v, hγv]
    exact analyticJ_eq_of_complexPoint_eq N _ _ hp
  · change X0Model.analyticJN N (γ₁ • UpperHalfPlane.ofComplex z) =
      X0Model.analyticJN N (γ₂ • v)
    rw [hz', hγv]
    exact mul_right_cancel₀ hd ha.symm

/-- The valuative chart identifies exactly the orbits of the level subgroup. -/
theorem complexPoint_eq_iff (N : ℕ) [NeZero N] (τ σ : UpperHalfPlane) :
    X0Model.complexPoint N τ = X0Model.complexPoint N σ ↔
      ∃ γ ∈ CongruenceSubgroup.Gamma0 N, γ • τ = σ := by
  refine ⟨fun h => ?_, complexPoint_eq_of_gamma0_orbit N τ σ⟩
  obtain ⟨γ, rfl⟩ := sl_orbit_of_complexPoint_eq N τ σ h
  obtain ⟨s, hs, hg⟩ := exists_stabilizer_germ_match N τ 1 γ (by simpa only [one_smul] using h)
  obtain ⟨δ, k, hδ, hk, hγ⟩ := rightOrbit_of_eventuallyEq_analyticJN N τ 1 γ s hs hg
  exact ⟨δ, hδ, by rw [hγ, mul_smul, hk, mul_one]⟩

/-- The prescribed smooth proper model, with the normalized chart and Laurent
expansions, at every nonzero level. -/
def model (N : ℕ) [NeZero N] : PreparedParam.X0Model N where
  X := X0Model.curve N
  overQ := X0Model.overQ N
  integral := X0Model.integral N
  proper := X0Model.proper N
  smooth := X0Model.smooth N
  functionField := X0Model.functionField N
  complexPoint τ := ⟨X0Model.complexPoint N τ, X0Model.complexPoint_overQ N τ⟩
  complexPoint_eq_iff τ σ := by
    erw [Subtype.mk_eq_mk]
    exact complexPoint_eq_iff N τ σ
  sectionExpansion U _ r := X0Model2.sectionExpansion N U r


end ZInQ.Manuscript.RC.X0Model3
