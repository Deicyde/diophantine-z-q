import Mathlib

/-! General topology used for the surjectivity of the analytic arc together with the
cusps: closures of images with one limit point, connectedness after removing finitely
many points with connected punctured neighbourhoods, and the open mapping theorem for
a holomorphic map from the upper half-plane to a complex curve. -/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped Manifold

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

/-- If a continuous map has limit `L` away from compact pieces of `S`, then the closure
of the image of `S` adds at most the point `L`. -/
theorem closure_image_subset_insert {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} (hf : Continuous f) {S : Set X} {L : Y}
    (h : ∀ V ∈ 𝓝 L, ∃ K ⊆ S, IsCompact K ∧ ∀ x ∈ S, x ∉ K → f x ∈ V) :
    closure (f '' S) ⊆ insert L (f '' S) := by
  intro y hy
  by_cases hyL : y = L
  · exact Or.inl hyL
  right
  obtain ⟨U, V, hU, hV, hyU, hLV, hUV⟩ := t2_separation hyL
  obtain ⟨K, hKS, hK, hKV⟩ := h V (hV.mem_nhds hLV)
  have hsub : f '' S ⊆ f '' K ∪ V := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxK : x ∈ K
    · exact Or.inl ⟨x, hxK, rfl⟩
    · exact Or.inr (hKV x hx hxK)
  have hcl : closure (f '' S) ⊆ f '' K ∪ closure V := by
    refine (closure_mono hsub).trans ?_
    rw [closure_union, (hK.image hf).isClosed.closure_eq]
  rcases hcl hy with hyK | hyV
  · exact image_mono hKS hyK
  · exact absurd (hyV) (fun hc => by
      have := mem_closure_iff.mp hc U hU hyU
      obtain ⟨z, hzU, hzV⟩ := this
      exact Set.disjoint_left.mp hUV hzU hzV)

/-- Removing one point with a connected punctured neighbourhood from an open
preconnected set leaves a preconnected set. -/
theorem isPreconnected_diff_singleton {X : Type*} [TopologicalSpace X] [T1Space X]
    {Y U : Set X} {c : X} (hY : IsOpen Y) (hYc : IsPreconnected Y) (hU : IsOpen U)
    (hcU : c ∈ U) (hUY : U ⊆ Y) (hUc : IsPreconnected (U \ {c})) :
    IsPreconnected (Y \ {c}) := by
  intro P Q hP hQ hcov hPne hQne
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hYc' : IsOpen (Y \ {c}) := hY.sdiff isClosed_singleton
  let P' := P ∩ (Y \ {c})
  let Q' := Q ∩ (Y \ {c})
  have hP' : IsOpen P' := hP.inter hYc'
  have hQ' : IsOpen Q' := hQ.inter hYc'
  have hdisj : Disjoint P' Q' := by
    rw [Set.disjoint_left]
    intro x hxP hxQ
    have : x ∈ (Y \ {c}) ∩ (P ∩ Q) := ⟨hxP.2, hxP.1, hxQ.1⟩
    rw [hempty] at this
    exact this
  have hUcov : U \ {c} ⊆ P' ∪ Q' := by
    intro x hx
    have hxY : x ∈ Y \ {c} := ⟨hUY hx.1, hx.2⟩
    rcases hcov hxY with h | h
    · exact Or.inl ⟨h, hxY⟩
    · exact Or.inr ⟨h, hxY⟩
  -- the main argument, symmetric in `P'` and `Q'`
  have key : ∀ {A B : Set X}, IsOpen A → IsOpen B → Disjoint A B →
      A ⊆ Y \ {c} → B ⊆ Y \ {c} → Y \ {c} ⊆ A ∪ B →
      (Y \ {c} ∩ A).Nonempty → (Y \ {c} ∩ B).Nonempty → U \ {c} ⊆ A → False := by
    intro A B hA hB hAB hAY hBY hcovAB hAne hBne hUA
    have hA2 : IsOpen (A ∪ U) := hA.union hU
    have hcovY : Y ⊆ (A ∪ U) ∪ B := by
      intro x hx
      by_cases hxc : x = c
      · exact Or.inl (Or.inr (hxc ▸ hcU))
      · rcases hcovAB ⟨hx, hxc⟩ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    obtain ⟨a, haY, haA⟩ := hAne
    obtain ⟨b, hbY, hbB⟩ := hBne
    obtain ⟨y, hyY, hyA, hyB⟩ := hYc (A ∪ U) B hA2 hB hcovY ⟨a, haY.1, Or.inl haA⟩
      ⟨b, hbY.1, hbB⟩
    have hyc : y ≠ c := (hBY hyB).2
    rcases hyA with hyA | hyU
    · exact Set.disjoint_left.mp hAB hyA hyB
    · exact Set.disjoint_left.mp hAB (hUA ⟨hyU, hyc⟩) hyB
  have hP'Y : P' ⊆ Y \ {c} := inter_subset_right
  have hQ'Y : Q' ⊆ Y \ {c} := inter_subset_right
  have hcov' : Y \ {c} ⊆ P' ∪ Q' := by
    intro x hx
    rcases hcov hx with h | h
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr ⟨h, hx⟩
  have hPne' : (Y \ {c} ∩ P').Nonempty := by
    obtain ⟨x, hx, hxP⟩ := hPne
    exact ⟨x, hx, hxP, hx⟩
  have hQne' : (Y \ {c} ∩ Q').Nonempty := by
    obtain ⟨x, hx, hxQ⟩ := hQne
    exact ⟨x, hx, hxQ, hx⟩
  rcases hUc.subset_or_subset hP' hQ' hdisj hUcov with h | h
  · exact key hP' hQ' hdisj hP'Y hQ'Y hcov' hPne' hQne' h
  · exact key hQ' hP' hdisj.symm hQ'Y hP'Y (by rw [union_comm]; exact hcov') hQne' hPne' h

/-- A preconnected space stays preconnected after removing finitely many points, each
of which has arbitrarily small open neighbourhoods with connected punctured part. -/
theorem isPreconnected_compl_of_finite {X : Type*} [TopologicalSpace X] [T1Space X]
    [PreconnectedSpace X]
    (hloc : ∀ c : X, ∀ O ∈ 𝓝 c, ∃ U ⊆ O, IsOpen U ∧ c ∈ U ∧ IsPreconnected (U \ {c}))
    (C : Set X) (hC : C.Finite) : IsPreconnected Cᶜ := by
  induction C, hC using Set.Finite.induction_on with
  | empty => simpa using isPreconnected_univ
  | @insert a s ha hs ih =>
    have hopen : IsOpen sᶜ := hs.isClosed.isOpen_compl
    have hsa : a ∈ sᶜ := ha
    obtain ⟨U, hUO, hU, haU, hUc⟩ := hloc a sᶜ (hopen.mem_nhds hsa)
    have := isPreconnected_diff_singleton hopen ih hU haU hUO hUc
    have he : (insert a s)ᶜ = sᶜ \ {a} := by
      ext x
      simp only [mem_compl_iff, mem_insert_iff, not_or, Set.mem_sdiff, mem_singleton_iff]
      tauto
    rw [he]
    exact this

/-- A punctured ball in a real normed space of dimension at least two is connected. -/
theorem isPreconnected_ball_diff_center {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : 1 < Module.rank ℝ E) (x : E) (r : ℝ) :
    IsPreconnected (Metric.ball x r \ {x}) := by
  by_cases hr : r ≤ 0
  · rw [Metric.ball_eq_empty.mpr hr, empty_sdiff]
    exact isPreconnected_empty
  push Not at hr
  have hS : IsConnected (Metric.sphere (0 : E) 1 ×ˢ Ioo (0 : ℝ) r) :=
    (isConnected_sphere hE 0 zero_le_one).prod (isConnected_Ioo hr)
  let g : E × ℝ → E := fun p => x + p.2 • p.1
  have hg : Continuous g := continuous_const.add (continuous_snd.smul continuous_fst)
  have himage : g '' (Metric.sphere (0 : E) 1 ×ˢ Ioo (0 : ℝ) r) = Metric.ball x r \ {x} := by
    ext y
    constructor
    · rintro ⟨⟨u, s⟩, ⟨hu, hs⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by simpa using hu
      have hnorm : ‖s • u‖ = s := by rw [norm_smul, hu', mul_one, Real.norm_of_nonneg hs.1.le]
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm]
        simp only [g, add_sub_cancel_left, hnorm]
        exact hs.2
      · intro hy
        have : s • u = 0 := by
          have h0 : x + s • u = x := hy
          simpa using h0
        rw [this, norm_zero] at hnorm
        exact (ne_of_gt hs.1) hnorm.symm
    · rintro ⟨hy, hyx⟩
      have hne : y - x ≠ 0 := sub_ne_zero.mpr hyx
      have hpos : 0 < ‖y - x‖ := norm_pos_iff.mpr hne
      refine ⟨⟨‖y - x‖⁻¹ • (y - x), ‖y - x‖⟩, ⟨?_, hpos, ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
      · rw [Metric.mem_ball, dist_eq_norm] at hy
        exact hy
      · simp only [g, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, add_sub_cancel]
  rw [← himage]
  exact (hS.image g hg.continuousOn).isPreconnected

theorem one_lt_rank_fin_one_complex : 1 < Module.rank ℝ (Fin 1 → ℂ) := by
  rw [(LinearEquiv.funUnique (Fin 1) ℝ ℂ).rank_eq, Complex.rank_real_complex]
  exact Nat.one_lt_ofNat

/-- On a space charted by `Fin 1 → ℂ`, every point has arbitrarily small open
neighbourhoods whose punctured part is connected. -/
theorem exists_open_punctured_preconnected {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Fin 1 → ℂ) M] (c : M) (O : Set M) (hO : O ∈ 𝓝 c) :
    ∃ U ⊆ O, IsOpen U ∧ c ∈ U ∧ IsPreconnected (U \ {c}) := by
  let e := chartAt (Fin 1 → ℂ) c
  have hc : c ∈ e.source := mem_chart_source _ c
  have hO' : O ∩ e.source ∈ 𝓝 c := inter_mem hO (e.open_source.mem_nhds hc)
  have himg : e '' (O ∩ e.source) ∈ 𝓝 (e c) := e.image_mem_nhds hc hO'
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp himg
  let U := e.source ∩ e ⁻¹' Metric.ball (e c) r
  have hUO : U ⊆ O := by
    intro q ⟨hq, hqb⟩
    obtain ⟨o, ⟨hoO, hos⟩, heo⟩ := hball hqb
    rw [← e.injOn hos hq heo]
    exact hoO
  refine ⟨U, hUO, e.isOpen_inter_preimage Metric.isOpen_ball, ⟨hc, Metric.mem_ball_self hr⟩, ?_⟩
  have hBt : Metric.ball (e c) r ⊆ e.target := by
    intro w hw
    obtain ⟨o, ⟨_, hos⟩, rfl⟩ := hball hw
    exact e.map_source hos
  have heq : e.symm '' (Metric.ball (e c) r \ {e c}) = U \ {c} := by
    ext q
    constructor
    · rintro ⟨w, ⟨hw, hwc⟩, rfl⟩
      have hwt := hBt hw
      refine ⟨⟨e.map_target hwt, by
        change e (e.symm w) ∈ Metric.ball (e c) r
        rw [e.right_inv hwt]; exact hw⟩, ?_⟩
      intro hq
      apply hwc
      rw [mem_singleton_iff] at hq ⊢
      rw [← hq, e.right_inv hwt]
    · rintro ⟨⟨hq, hqb⟩, hqc⟩
      refine ⟨e q, ⟨hqb, ?_⟩, e.left_inv hq⟩
      intro h
      apply hqc
      exact e.injOn hq hc h
  rw [← heq]
  exact (isPreconnected_ball_diff_center one_lt_rank_fin_one_complex (e c) r).image _
    (e.continuousOn_symm.mono (sdiff_subset.trans hBt))

/-- Open mapping theorem for a holomorphic map from the upper half-plane to a
complex curve: if the map is not constant near `τ`, its range is a neighbourhood
of the image of `τ`. -/
theorem range_mem_nhds_of_mdifferentiable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Fin 1 → ℂ) M] [IsManifold 𝓘(ℂ, Fin 1 → ℂ) 1 M]
    {f : ℍ → M} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) f) (τ : ℍ)
    (hnc : ¬ ∀ᶠ z in 𝓝 τ, f z = f τ) : Set.range f ∈ 𝓝 (f τ) := by
  let e := chartAt (Fin 1 → ℂ) (f τ)
  have hcont : Continuous f := hf.continuous
  have hsrc : f ⁻¹' e.source ∈ 𝓝 τ :=
    hcont.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds (mem_chart_source _ _))
  let φ : M → ℂ := fun q => extChartAt 𝓘(ℂ, Fin 1 → ℂ) (f τ) q 0
  let h : ℍ → ℂ := φ ∘ f
  have hmd : ∀ σ : ℍ, f σ ∈ e.source → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) h σ := by
    intro σ hσ
    have h1 : MDifferentiableAt 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, Fin 1 → ℂ)
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (f τ)) (f σ) := mdifferentiableAt_extChartAt hσ
    have h2 : MDifferentiableAt 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ)
        (fun v : Fin 1 → ℂ => v 0) (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (f τ) (f σ)) :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).mdifferentiableAt
    exact (h2.comp _ h1).comp σ (hf σ)
  let g : ℂ → ℂ := h ∘ UpperHalfPlane.ofComplex
  let W : Set ℂ := {z | 0 < z.im} ∩ UpperHalfPlane.ofComplex ⁻¹' (f ⁻¹' e.source)
  have hWopen : W ∈ 𝓝 (τ : ℂ) := by
    have h1 : {z : ℂ | 0 < z.im} ∈ 𝓝 (τ : ℂ) :=
      UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos
    have h2 : UpperHalfPlane.ofComplex ⁻¹' (f ⁻¹' e.source) ∈ 𝓝 (τ : ℂ) := by
      have hc : ContinuousAt UpperHalfPlane.ofComplex (τ : ℂ) :=
        UpperHalfPlane.ofComplex.continuousAt (by
          simpa [UpperHalfPlane.ofComplex] using τ.im_pos)
      apply hc.preimage_mem_nhds
      rw [UpperHalfPlane.ofComplex_apply]
      exact hsrc
    exact inter_mem h1 h2
  have hdiff : ∀ z ∈ W, DifferentiableAt ℂ g z := by
    rintro z ⟨hz, hzs⟩
    let σ : ℍ := ⟨z, hz⟩
    have hσ : UpperHalfPlane.ofComplex z = σ := UpperHalfPlane.ofComplex_apply σ
    have := UpperHalfPlane.mdifferentiableAt_iff.mp (hmd σ (by rw [← hσ]; exact hzs))
    exact this
  have hWo : IsOpen (interior W) := isOpen_interior
  have hanalytic : AnalyticAt ℂ g (τ : ℂ) :=
    DifferentiableOn.analyticAt (s := interior W)
      (fun z hz => (hdiff z (interior_subset hz)).differentiableWithinAt)
      (hWo.mem_nhds (mem_interior_iff_mem_nhds.mpr hWopen))
  have hgτ : g τ = φ (f τ) := by
    simp only [g, h, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
  -- the chart is injective on its source, through the single coordinate
  have hinj : ∀ q₁ ∈ e.source, ∀ q₂ ∈ e.source, φ q₁ = φ q₂ → q₁ = q₂ := by
    intro q₁ h₁ q₂ h₂ hq
    apply e.injOn h₁ h₂
    funext i
    fin_cases i
    exact hq
  rcases hanalytic.eventually_constant_or_nhds_le_map_nhds_aux with hconst | hopen
  · exfalso
    apply hnc
    have hτ : ∀ᶠ z : ℍ in 𝓝 τ, (z : ℂ) ∈ {w : ℂ | g w = g τ} ∩ W := by
      have hc : Continuous (fun z : ℍ => (z : ℂ)) := UpperHalfPlane.continuous_coe
      exact hc.continuousAt.preimage_mem_nhds (inter_mem hconst hWopen)
    
    filter_upwards [hτ] with z ⟨hz, hzW⟩
    have hzs : f z ∈ e.source := by
      have := hzW.2
      simpa only [mem_preimage, UpperHalfPlane.ofComplex_apply] using this
    apply hinj _ hzs _ (mem_chart_source _ _)
    rw [← hgτ]
    simpa only [Set.mem_ofPred_eq, g, h, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hz
  · have himg : g '' W ∈ 𝓝 (φ (f τ)) := by
      rw [← hgτ]
      exact hopen (image_mem_map hWopen)
    have hφ : ContinuousAt φ (f τ) := by
      have h1 : ContinuousAt (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (f τ)) (f τ) :=
        continuousAt_extChartAt (f τ)
      exact (continuous_apply 0).continuousAt.comp h1
    have hT : e.source ∩ φ ⁻¹' (g '' W) ∈ 𝓝 (f τ) :=
      inter_mem (e.open_source.mem_nhds (mem_chart_source _ _)) (hφ.preimage_mem_nhds himg)
    refine mem_of_superset hT ?_
    rintro q ⟨hq, z, hzW, hgz⟩
    refine ⟨UpperHalfPlane.ofComplex z, ?_⟩
    exact hinj _ hzW.2 _ hq hgz

end ZInQ.Manuscript.RC.CuspFormDifferentials
