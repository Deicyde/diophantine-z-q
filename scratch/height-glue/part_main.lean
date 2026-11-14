
/-! ## The two leaves of §1 proved: Hausdorffness and immersion

`AnalyticPointsT2` is proved from metrization2's `productMapLocalStructure` (the local structure
of `𝒢 ×_{𝓞_L} 𝒢` at complex points) applied to the division morphism `(x, y) ↦ x y⁻¹`, and from
`pts_eq_of_evalAt` (a complex point of an affine open is determined by its values).

`IsImmersiveAtZero` is proved for **every** analytic uniformization with a discrete kernel, by
metrization2's argument for `jacDetNondegenerate_of` (steps 2-5: translation through
`productMapLocalStructure`, constancy along a line, discreteness). -/

section T2

open ZInQ.Metrization ZInQ.Metrization2 MonoidalCategory CartesianMonoidalCategory

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L) (τ : L →+* ℂ)

theorem isOpen_evalSet (V : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, V)) (t : Set ℂ) (ht : IsOpen t) :
    @IsOpen _ (anTop 𝒢 τ) {p : 𝒢.Pts τ | ⊤ ≤ p.left ⁻¹ᵁ V ∧ 𝒢.evalAt p V s ∈ t} :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨V, s, t, ht, rfl⟩

theorem isOpen_ptsIn (V : 𝒢.G.left.Opens) :
    @IsOpen _ (anTop 𝒢 τ) {p : 𝒢.Pts τ | ⊤ ≤ p.left ⁻¹ᵁ V} := by
  have := isOpen_evalSet 𝒢 τ V 0 Set.univ isOpen_univ
  simpa using this

theorem continuousOn_evalAt (V : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, V)) :
    @ContinuousOn _ _ (anTop 𝒢 τ) _ (fun p => 𝒢.evalAt p V s) {p | ⊤ ≤ p.left ⁻¹ᵁ V} := by
  letI := anTop 𝒢 τ
  rw [continuousOn_iff']
  intro t ht
  refine ⟨_, isOpen_evalSet 𝒢 τ V s t ht, ?_⟩
  ext p
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
  tauto

/-- The division morphism `(x, y) ↦ x y⁻¹` of the group scheme `𝒢`. -/
noncomputable def divMor : 𝒢.G ⊗ 𝒢.G ⟶ 𝒢.G := (𝒢.G ◁ GrpObj.inv (X := 𝒢.G)) ≫ μ[𝒢.G]

theorem lift_divMor (x y : 𝒢.Pts τ) : lift x y ≫ divMor 𝒢 = x * y⁻¹ := by
  rw [divMor, ← Category.assoc, lift_whiskerLeft]
  rfl

/-- **`AnalyticPointsT2`, proved** (no hypotheses): the analytic topology on `𝒢(ℂ)_τ` is
Hausdorff. -/
theorem analyticPointsT2 : AnalyticPointsT2 := by
  intro K _ A L _ _ _ 𝒢 τ
  letI := anTop 𝒢 τ
  refine ⟨fun p q hpq => ?_⟩
  set r : 𝒢.Pts τ := lift p q ≫ divMor 𝒢 with hr
  have hr1 : r ≠ 1 := by
    rw [hr, lift_divMor]
    intro h
    exact hpq (mul_inv_eq_one.mp h)
  let pt : Spec (CommRingCat.of ℂ) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨U, hU, mU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show r.left pt ∈ (⊤ : 𝒢.G.left.Opens) from trivial)
  have hrU : ⊤ ≤ r.left ⁻¹ᵁ U := top_le_of_mem r.left U pt mU
  -- a section `s` and a radius `δ` separating `r` from `1` (if `1 ∈ U(ℂ)`)
  obtain ⟨s, δ, hδ, hsep⟩ : ∃ (s : Γ(𝒢.G.left, U)) (δ : ℝ), 0 < δ ∧
      (⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ U → δ ≤ ‖𝒢.evalAt r U s - 𝒢.evalAt (1 : 𝒢.Pts τ) U s‖) := by
    by_cases h1 : ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ U
    · have : ∃ s : Γ(𝒢.G.left, U), 𝒢.evalAt r U s ≠ 𝒢.evalAt (1 : 𝒢.Pts τ) U s := by
        by_contra hcon
        push_neg at hcon
        exact hr1 (pts_eq_of_evalAt 𝒢 U hU r 1 hrU h1 hcon)
      obtain ⟨s, hs⟩ := this
      exact ⟨s, _, norm_pos_iff.mpr (sub_ne_zero.mpr hs), fun _ => le_rfl⟩
    · exact ⟨0, 1, one_pos, fun h => absurd h h1⟩
  obtain ⟨V₁, V₂, n, a, c, b, d, hV₁, hV₂, hne, hall⟩ :=
    productMapLocalStructure K A A A L 𝒢 𝒢 𝒢 (divMor 𝒢) τ U s p q hrU
  -- the functions `H = Σ c ⊗ d` and `N = Σ a ⊗ b` on `V₁(ℂ) × V₂(ℂ)`
  set S : Set (𝒢.Pts τ × 𝒢.Pts τ) :=
    {p | ⊤ ≤ p.left ⁻¹ᵁ V₁} ×ˢ {p | ⊤ ≤ p.left ⁻¹ᵁ V₂} with hS
  let H : 𝒢.Pts τ × 𝒢.Pts τ → ℂ := fun z =>
    ∑ k, 𝒢.evalAt z.1 V₁ (c k) * 𝒢.evalAt z.2 V₂ (d k)
  let N : 𝒢.Pts τ × 𝒢.Pts τ → ℂ := fun z =>
    ∑ k, 𝒢.evalAt z.1 V₁ (a k) * 𝒢.evalAt z.2 V₂ (b k)
  have hS_open : IsOpen S := (isOpen_ptsIn 𝒢 τ V₁).prod (isOpen_ptsIn 𝒢 τ V₂)
  have hc1 : ∀ s₁ : Γ(𝒢.G.left, V₁), ContinuousOn (fun z : 𝒢.Pts τ × 𝒢.Pts τ =>
      𝒢.evalAt z.1 V₁ s₁) S := fun s₁ =>
    (continuousOn_evalAt 𝒢 τ V₁ s₁).comp continuous_fst.continuousOn (fun z hz => hz.1)
  have hc2 : ∀ s₂ : Γ(𝒢.G.left, V₂), ContinuousOn (fun z : 𝒢.Pts τ × 𝒢.Pts τ =>
      𝒢.evalAt z.2 V₂ s₂) S := fun s₂ =>
    (continuousOn_evalAt 𝒢 τ V₂ s₂).comp continuous_snd.continuousOn (fun z hz => hz.2)
  have hH : ContinuousOn H S :=
    continuousOn_finset_sum _ fun k _ => (hc1 (c k)).mul (hc2 (d k))
  have hN : ContinuousOn N S :=
    continuousOn_finset_sum _ fun k _ => (hc1 (a k)).mul (hc2 (b k))
  -- the open set `W ∋ (p, q)`
  set W : Set (𝒢.Pts τ × 𝒢.Pts τ) := S ∩ (fun z => (H z, N z)) ⁻¹'
    {w : ℂ × ℂ | w.1 ≠ 0 ∧ ‖w.2 / w.1 - 𝒢.evalAt r U s‖ < δ / 2} with hW
  have hW_open : IsOpen W := by
    refine (hH.prodMk hN).isOpen_inter_preimage hS_open ?_
    have : IsOpen {w : ℂ × ℂ | w.1 ≠ 0} := isOpen_ne_fun continuous_fst continuous_const
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨hw1, hw2⟩
    have hcont : ContinuousAt (fun w : ℂ × ℂ => ‖w.2 / w.1 - 𝒢.evalAt r U s‖) w :=
      ((continuous_snd.continuousAt.div continuous_fst.continuousAt hw1).sub
        continuousAt_const).norm
    exact Filter.inter_mem (this.mem_nhds hw1)
      (hcont.preimage_mem_nhds (Iio_mem_nhds hw2))
  have hpqW : (p, q) ∈ W := by
    refine ⟨⟨hV₁, hV₂⟩, hne, ?_⟩
    obtain ⟨-, heq⟩ := hall p q hV₁ hV₂ hne
    show ‖N (p, q) / H (p, q) - 𝒢.evalAt r U s‖ < δ / 2
    have : N (p, q) / H (p, q) = 𝒢.evalAt r U s := by
      rw [div_eq_iff hne]; exact heq.symm
    rw [this, sub_self, norm_zero]
    linarith
  obtain ⟨u, v, hu, hv, hpu, hqv, huv⟩ := isOpen_prod_iff.mp hW_open p q hpqW
  refine ⟨u, v, hu, hv, hpu, hqv, Set.disjoint_left.mpr fun x hxu hxv => ?_⟩
  obtain ⟨⟨hx1, hx2⟩, hxH, hxN⟩ := huv (show (x, x) ∈ u ×ˢ v from ⟨hxu, hxv⟩)
  obtain ⟨hmem, heq⟩ := hall x x hx1 hx2 hxH
  have hxx : lift x x ≫ divMor 𝒢 = 1 := by rw [lift_divMor, mul_inv_cancel]
  rw [hxx] at hmem heq
  have hval : N (x, x) / H (x, x) = 𝒢.evalAt (1 : 𝒢.Pts τ) U s := by
    rw [div_eq_iff hxH]; exact heq.symm
  have hlt : ‖𝒢.evalAt (1 : 𝒢.Pts τ) U s - 𝒢.evalAt r U s‖ < δ / 2 := by
    have := hxN; simp only [Set.mem_setOf_eq] at this; rwa [hval] at this
  have hge := hsep hmem
  rw [norm_sub_rev] at hge
  linarith

end T2

section Immersion

open ZInQ.Metrization ZInQ.Metrization2

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **Every analytic uniformization with a discrete kernel is immersive at `0`** (proved, no
hypotheses; no lattice condition, no `g = dim A`). Steps 2-5 of metrization2's
`jacDetNondegenerate_of`, copied with the hypothesis "every regular function near `ξ` kills `v`"
in place of step 1. -/
theorem isImmersiveAtZero_of_discrete (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} [hdisc : DiscreteTopology Λ] {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) : IsImmersiveAtZero 𝒢 τ Φ := by
  intro v hv0
  by_contra hcon
  push_neg at hcon
  have hv2 : ∀ (V : 𝒢.G.left.Opens) (_ : 𝒢.genericUnit ∈ V) (b : Γ(𝒢.G.left, V)),
      fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V b) 0 v = 0 :=
    fun V m b => hcon V b (zero_mem_dom 𝒢 hΦ V m)
  -- an affine open around `ξ`
  obtain ⟨U, hU, mU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show 𝒢.genericUnit ∈ (⊤ : 𝒢.G.left.Opens) from trivial)
  have hdomU : IsOpen (𝒢.dom Φ U) := hΦ.2.2.2.1 U
  have h0U : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := zero_mem_dom 𝒢 hΦ U mU
  have hcont : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
  have hBopen : IsOpen {t : ℂ | t • v ∈ 𝒢.dom Φ U} := hdomU.preimage hcont
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hBopen 0 (by simp [h0U])
  have hconst : ∀ t ∈ Metric.ball (0 : ℂ) r, Φ (t • v) = Φ 0 := by
    intro t ht
    have hderiv : ∀ (s : Γ(𝒢.G.left, U)), ∀ t₀ ∈ Metric.ball (0 : ℂ) r,
        HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t • v)) U s) 0 t₀ := by
      intro s t₀ ht₀
      have h3 := hasDerivAt_line_zero 𝒢 productMapLocalStructure hΦ v hv2 U s (t₀ • v)
        (hball ht₀)
      have h4 : HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t₀ • v + (t - t₀) • v)) U s) 0 t₀ := by
        have h3' : HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t₀ • v + t • v)) U s) 0 (t₀ - t₀) := by
          rw [sub_self]; exact h3
        exact h3'.comp_sub_const t₀ t₀
      refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [← add_smul, add_sub_cancel]
    apply pts_eq_of_evalAt 𝒢 U hU _ _ (hball ht) h0U
    intro s
    have := (Metric.isOpen_ball).is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
      (fun t₀ ht₀ => (hderiv s t₀ ht₀).differentiableAt.differentiableWithinAt)
      (fun t₀ ht₀ => (hderiv s t₀ ht₀).deriv) ht (Metric.mem_ball_self hr)
    simpa using this
  have h0 : Φ 0 = 1 := au_map_zero hΦ
  have hmem : ∀ t ∈ Metric.ball (0 : ℂ) r, t • v ∈ Λ := fun t ht =>
    (hΦ.2.1 _).mp ((hconst t ht).trans h0)
  obtain ⟨u, hu, hpre⟩ := isOpen_induced_iff.mp (isOpen_discrete ({0} : Set Λ))
  have hu0 : (0 : Fin g → ℂ) ∈ u := by
    have : (0 : Λ) ∈ ({0} : Set Λ) := rfl
    rw [← hpre] at this
    exact this
  have hev1 : ∀ᶠ t in 𝓝 (0 : ℂ), t • v ∈ u :=
    hcont.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hu.mem_nhds hu0)
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ Metric.ball (0 : ℂ) r := Metric.ball_mem_nhds 0 hr
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t • v ∈ u ∧ t ∈ Metric.ball (0 : ℂ) r :=
    nhdsWithin_le_nhds (hev1.and hev2)
  obtain ⟨t, ⟨htu, htb⟩, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hin : (⟨t • v, hmem t htb⟩ : Λ) ∈ Subtype.val ⁻¹' u := htu
  rw [hpre] at hin
  have : t • v = 0 := congrArg Subtype.val hin
  rcases smul_eq_zero.mp this with h | h
  · exact ht0 h
  · exact hv0 h

/-- **`ImmersiveUniformizationExists` is equivalent to the kernel's
`AnalyticUniformizationExists`** (proved). -/
theorem immersiveUniformizationExists_of (hE : AnalyticUniformizationExists) :
    ImmersiveUniformizationExists := by
  intro K _ A L _ _ _ 𝒢 τ
  obtain ⟨g, Λ, Φ, hd, hl, hu⟩ := hE K A L 𝒢 τ
  exact ⟨g, Λ, Φ, hd, hl, hu, isImmersiveAtZero_of_discrete 𝒢 τ hu⟩

end Immersion

/-! ## Main results -/

/-- **`AnalyticUniformizationUnique` (kernel AN3U) from the kernel's `AnalyticUniformizationExists`
(AN3) alone.** -/
theorem analyticUniformizationUnique_of_exists (hE : AnalyticUniformizationExists) :
    AnalyticUniformizationUnique :=
  analyticUniformizationUnique_of (immersiveUniformizationExists_of hE) analyticPointsT2

/-- An abelian variety has finite dimension (copied from unif-dims' copy of metrization's
`abVar_dim_finite`, `scratch/unif-dims/Combined.lean` l. 4559). -/
theorem abVar_dim_finite (K : Type) [Field K] (A : AbVar K) :
    ∃ n : ℕ, A.dim = (n : WithBot ℕ∞) := by
  haveI : Nonempty A.X.left :=
    ⟨η[A.X].left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))⟩
  exact G0Dim.dim_finite A.X.left A.X.hom

/-- The kernel's `AnalyticUniformizationExists` from the textbook leaf T35
(`ZInQ.LeafPush2.UniformizationExists` = `TextbookLeaves.t35`), via metrization2's transport. -/
theorem analyticUniformizationExists_of_t35 (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    AnalyticUniformizationExists := by
  intro K _ A L _ _ _ 𝒢 τ
  obtain ⟨g, hg⟩ := abVar_dim_finite K A
  exact ⟨g, ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT35
    K A L 𝒢 τ g hg⟩

/-- **`AnalyticUniformizationUnique` from the textbook leaf T35.** -/
theorem analyticUniformizationUnique_of_t35 (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    AnalyticUniformizationUnique :=
  analyticUniformizationUnique_of_exists (analyticUniformizationExists_of_t35 hT35)
