

open ZInQ.HeightSplit


/-- **`UniformizationDim`, from the textbook leaf T35** (proved). T35 (through metrization2's
transport) gives a full-lattice analytic uniformization `Φ'` of dimension `dim A`; a full-lattice
`Φ` of dimension `g` and `Φ'` factor through each other by surjective `ℂ`-linear maps
(`exists_linear_factor`, with `analyticPointsT2` and `isImmersiveAtZero_of_discrete`), so
`g = dim A`. -/
theorem uniformizationDim_of_t35 (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    UniformizationDim := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hd hz hΦ
  obtain ⟨g', hg'⟩ := abVar_dim_finite K A
  obtain ⟨Λ', Φ', hd', hz', hΦ'⟩ :=
    ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT35 K A L 𝒢 τ g' hg'
  haveI := hd; haveI := hd'; haveI := hz; haveI := hz'
  have hT2 := analyticPointsT2 K A L 𝒢 τ
  obtain ⟨M, hM, -⟩ :=
    exists_linear_factor hT2 Λ' hΦ' (isImmersiveAtZero_of_discrete 𝒢 τ hΦ') hΦ
  obtain ⟨M', hM', -⟩ :=
    exists_linear_factor hT2 Λ hΦ (isImmersiveAtZero_of_discrete 𝒢 τ hΦ) hΦ'
  have h1 := M.finrank_range_le
  have h2 := M'.finrank_range_le
  rw [LinearMap.range_eq_top.mpr hM, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h1
  rw [LinearMap.range_eq_top.mpr hM', finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h2
  rw [hg', le_antisymm h1 h2]

/-- **`MetrizationOfUniformization`, proved** (no hypotheses): the lattice and line from
`ZInQ.Contrib.Dim.hodgeLatticeTheorem` (in the build), the coefficient maps from metrization's
`jacDetDescends` (proved, unif-dims' kernel-type copy), nonvanishing from metrization2's
`jacDetNondegenerate` (proved); the assembly is metrization's `exists_metrization_of_dim` with the
given uniformizations in place of `AnalyticUniformizationOfDim`. -/
theorem metrizationOfUniformization : MetrizationOfUniformization := by
  intro K _ _ A L _ _ _ 𝒢 g hg hU
  obtain ⟨hfr, hlat⟩ := ZInQ.Contrib.Dim.hodgeLatticeTheorem K A L 𝒢 g hg
  choose Λ Φ hdisc hZ hΦ using hU
  choose c hc using fun τ => ZInQ.Metrization.jacDetDescends K A L 𝒢 τ g (Λ τ) (Φ τ) (hΦ τ)
  have hc0 : ∀ τ, c τ ≠ 0 := by
    intro τ h0
    haveI := hdisc τ
    obtain ⟨f, hf⟩ :=
      ZInQ.Metrization2.jacDetNondegenerate K A L 𝒢 τ g hg (Λ τ) (Φ τ) (hZ τ) (hΦ τ)
    apply hf
    rw [← hc τ f, h0]
    rfl
  exact ⟨{ model := 𝒢
           hodge :=
            { lattice := 𝒢.detLattice g
              finrank_eq_one := hfr
              isLattice := hlat
              periods := Λ
              periods_discrete := hdisc
              periods_isZLattice := hZ
              coeff := c
              coeff_ne_zero := hc0 }
           lattice_eq := rfl
           arch := fun τ => ⟨Φ τ, hΦ τ, hc τ⟩ }, rfl⟩

/-- **`NeronMetrizable` from the textbook leaf T35** (proved). -/
theorem neronMetrizable_of_t35 (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    NeronMetrizable :=
  neronMetrizable_of (analyticUniformizationExists_of_t35 hT35) (uniformizationDim_of_t35 hT35)
    metrizationOfUniformization

/-- **height-split's whole `HeightGlue` bundle from the textbook leaf T35** (proved). -/
theorem heightGlue_of_t35 (hT35 : ZInQ.LeafPush2.UniformizationExists) : HeightGlue :=
  ⟨analyticUniformizationExists_of_t35 hT35, analyticUniformizationUnique_of_t35 hT35,
    uniformizationDim_of_t35 hT35, metrizationOfUniformization⟩

/-- The same bundle from the kernel's own Prop `AnalyticUniformizationExists` plus
`UniformizationDim` (T35 is used only for `UniformizationDim`). -/
theorem heightGlue_of_exists_dim (hE : AnalyticUniformizationExists) (hD : UniformizationDim) :
    HeightGlue :=
  ⟨hE, analyticUniformizationUnique_of_exists hE, hD, metrizationOfUniformization⟩

/-- **The six height rows (H-14 to H-19) from height-split's nine published-form leaves and the
textbook leaf T35 alone** (proved): height-split's `heightRows_of` with its glue bundle
`HeightGlue` supplied by `heightGlue_of_t35`. -/
theorem heightRows_of_t35 (l : ZInQ.HeightSplit.HeightLeaves)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.LeafPush2.R18_Javanpeykar ∧ ZInQ.DefFaltings.R19_GaudronRemond ∧
      ZInQ.DefFaltings.R20_FaltingsLemma5 ∧ ZInQ.DefFaltings.R21_Bost ∧
      ZInQ.LeafPush2.R22_Pazuki ∧ ZInQ.DefFaltings.StableHeightFinite :=
  ZInQ.HeightSplit.heightRows_of l (heightGlue_of_t35 hT35)
