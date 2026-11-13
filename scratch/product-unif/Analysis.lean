import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # product-unif: the elementary analysis behind `ProductUnifSplits` (Mathlib only)

* `rcore H` (resp. `ccore H`): the largest real (resp. complex) subspace contained in an additive
  subgroup `H`.
* `exists_isolated`: for a closed subgroup `H` of a finite-dimensional real space and a subspace
  `W` meeting `rcore H` in `0`, the points of `H ∩ W` are uniformly isolated.
* `exists_countable_add`: a closed subgroup is `rcore H + S` with `S` countable.
* `rcore_sup_eq_top`: if `H₁ + H₂ = E` for closed subgroups, then `rcore H₁ ⊔ rcore H₂ = ⊤`
  (measure zero of proper subspaces).
* `isClosed_of_local`: a subgroup cut out near `0` by functions continuous there is closed.
* `rcore_le_ccore`: if near `0` the subgroup is cut out by holomorphic functions, its real core
  is complex (identity theorem).
* `rcore_eq_bot_of_discrete`: the real core of a discrete subgroup is `0`. -/

namespace ZInQ.ProductUnif

open Topology Filter MeasureTheory Metric

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The real core `{v | ℝ v ⊆ H}` of an additive subgroup. -/
def rcore (H : AddSubgroup E) : Submodule ℝ E where
  carrier := {v | ∀ t : ℝ, t • v ∈ H}
  add_mem' := by
    intro a b ha hb t
    rw [smul_add]
    exact H.add_mem (ha t) (hb t)
  zero_mem' := by
    intro t
    rw [smul_zero]
    exact H.zero_mem
  smul_mem' := by
    intro c a ha t
    rw [smul_smul]
    exact ha _

theorem mem_rcore {H : AddSubgroup E} {v : E} : v ∈ rcore H ↔ ∀ t : ℝ, t • v ∈ H := Iff.rfl

theorem rcore_le_self {H : AddSubgroup E} {v : E} (hv : v ∈ rcore H) : v ∈ H := by
  simpa using hv 1

variable [FiniteDimensional ℝ E]

/-- **Isolation in a complement of the real core.** -/
theorem exists_isolated (H : AddSubgroup E) (hH : IsClosed (H : Set E)) (W : Submodule ℝ E)
    (hW : rcore H ⊓ W = ⊥) : ∃ ε > 0, ∀ c ∈ H, c ∈ W → ‖c‖ < ε → c = 0 := by
  by_contra hne
  push Not at hne
  choose c hcH hcW hcn hc0 using fun n : ℕ => hne (1 / ((n : ℝ) + 1)) (by positivity)
  set u : ℕ → E := fun n => ‖c n‖⁻¹ • c n with hu_def
  have hu : ∀ n, u n ∈ sphere (0 : E) 1 := by
    intro n
    have : ‖c n‖ ≠ 0 := norm_ne_zero_iff.mpr (hc0 n)
    simp [u, norm_smul, this]
  obtain ⟨v, hv, φ, hφ, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hu
  have hc_lim : Tendsto c atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hcn n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hc_lim' : Tendsto (fun n => c (φ n)) atTop (𝓝 0) := hc_lim.comp hφ.tendsto_atTop
  have hvW : v ∈ W :=
    (W.closed_of_finiteDimensional).mem_of_tendsto hlim
      (Eventually.of_forall fun n => W.smul_mem _ (hcW _))
  have hvR : v ∈ rcore H := by
    intro t
    have h1 : Tendsto (fun n => t • u (φ n)) atTop (𝓝 (t • v)) := hlim.const_smul t
    have h2 : Tendsto (fun n => (⌊t / ‖c (φ n)‖⌋ : ℤ) • c (φ n) - t • u (φ n)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hc_lim'.norm)
      have ha : ‖c (φ n)‖ ≠ 0 := norm_ne_zero_iff.mpr (hc0 _)
      have : (⌊t / ‖c (φ n)‖⌋ : ℤ) • c (φ n) - t • u (φ n) =
          (((⌊t / ‖c (φ n)‖⌋ : ℤ) : ℝ) - t / ‖c (φ n)‖) • c (φ n) := by
        rw [sub_smul, ← Int.cast_smul_eq_zsmul ℝ, hu_def]
        simp only
        rw [smul_smul, div_eq_mul_inv]
      rw [this, norm_smul, Real.norm_eq_abs]
      have hfl : |(((⌊t / ‖c (φ n)‖⌋ : ℤ) : ℝ) - t / ‖c (φ n)‖)| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [Int.lt_floor_add_one (t / ‖c (φ n)‖)]
        · linarith [Int.floor_le (t / ‖c (φ n)‖)]
      calc |(((⌊t / ‖c (φ n)‖⌋ : ℤ) : ℝ) - t / ‖c (φ n)‖)| * ‖c (φ n)‖
          ≤ 1 * ‖c (φ n)‖ := mul_le_mul_of_nonneg_right hfl (norm_nonneg _)
        _ = ‖c (φ n)‖ := one_mul _
    have h3 := h1.add h2
    simp only [add_sub_cancel, add_zero] at h3
    exact hH.mem_of_tendsto h3 (Eventually.of_forall fun n => H.zsmul_mem (hcH _) _)
  have hv0 : v = 0 := by
    have : v ∈ rcore H ⊓ W := ⟨hvR, hvW⟩
    rw [hW] at this
    exact this
  simp [hv0] at hv

/-- **A closed subgroup is its real core plus a countable set.** -/
theorem exists_countable_add (H : AddSubgroup E) (hH : IsClosed (H : Set E)) :
    ∃ S : Set E, S.Countable ∧ ∀ h ∈ H, ∃ r ∈ rcore H, ∃ s ∈ S, h = r + s := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (rcore H)
  obtain ⟨ε, hε, hiso⟩ := exists_isolated H hH W hW.inf_eq_bot
  set S : Set E := {w | w ∈ H ∧ w ∈ W}
  have hsep : Pairwise fun x y : S => ε ≤ dist x y := by
    intro x y hxy
    by_contra hlt
    push Not at hlt
    apply hxy
    have h0 := hiso ((x : E) - y) (H.sub_mem x.2.1 y.2.1) (W.sub_mem x.2.2 y.2.2)
      (by rw [← dist_eq_norm]; exact hlt)
    exact Subtype.ext (sub_eq_zero.mp h0)
  have : DiscreteTopology S := DiscreteTopology.of_forall_le_dist hε hsep
  have : Countable S := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  refine ⟨S, Set.countable_coe_iff.mp inferInstance, fun h hh => ?_⟩
  have hmem : h ∈ rcore H ⊔ W := by rw [hW.sup_eq_top]; trivial
  obtain ⟨r, hr, w, hw, rfl⟩ := Submodule.mem_sup.mp hmem
  refine ⟨r, hr, w, ⟨?_, hw⟩, rfl⟩
  have : w = (r + w) - r := by abel
  rw [this]
  exact H.sub_mem hh (rcore_le_self hr)

variable [MeasurableSpace E] [BorelSpace E]

/-- **`H₁ + H₂ = E` forces `rcore H₁ ⊔ rcore H₂ = ⊤`** (a proper subspace is null). -/
theorem rcore_sup_eq_top (H₁ H₂ : AddSubgroup E) (h₁ : IsClosed (H₁ : Set E))
    (h₂ : IsClosed (H₂ : Set E)) (hs : ∀ x : E, ∃ a ∈ H₁, ∃ b ∈ H₂, a + b = x) :
    rcore H₁ ⊔ rcore H₂ = ⊤ := by
  by_contra hne
  obtain ⟨S₁, hS₁, hd₁⟩ := exists_countable_add H₁ h₁
  obtain ⟨S₂, hS₂, hd₂⟩ := exists_countable_add H₂ h₂
  set P := rcore H₁ ⊔ rcore H₂
  let μ : Measure E := Measure.addHaar
  have hP : μ (P : Set E) = 0 := Measure.addHaar_submodule μ P hne
  have : Countable S₁ := hS₁.to_subtype
  have : Countable S₂ := hS₂.to_subtype
  have hcov : (Set.univ : Set E) ⊆
      ⋃ p : S₁ × S₂, (fun x => -((p.1 : E) + p.2) + x) ⁻¹' (P : Set E) := by
    intro x _
    obtain ⟨a, ha, b, hb, rfl⟩ := hs x
    obtain ⟨r₁, hr₁, s₁, hs₁, rfl⟩ := hd₁ a ha
    obtain ⟨r₂, hr₂, s₂, hs₂, rfl⟩ := hd₂ b hb
    refine Set.mem_iUnion.mpr ⟨(⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩), ?_⟩
    show -(s₁ + s₂) + (r₁ + s₁ + (r₂ + s₂)) ∈ P
    have : -(s₁ + s₂) + (r₁ + s₁ + (r₂ + s₂)) = r₁ + r₂ := by abel
    rw [this]
    exact P.add_mem (Submodule.mem_sup_left hr₁) (Submodule.mem_sup_right hr₂)
  have hnull : μ (⋃ p : S₁ × S₂, (fun x => -((p.1 : E) + p.2) + x) ⁻¹' (P : Set E)) = 0 := by
    refine measure_iUnion_null fun p => ?_
    rw [measure_preimage_add]
    exact hP
  have hu : μ Set.univ = 0 := measure_mono_null hcov hnull
  exact (Measure.measure_univ_ne_zero.mpr (NeZero.ne μ)) hu

end Real

section Closed

variable {E : Type*} [NormedAddCommGroup E]

/-- **A subgroup cut out near `0` by functions continuous there is closed.** -/
theorem isClosed_of_local (H : AddSubgroup E) (N : Set E) (hN : IsOpen N) (h0 : (0 : E) ∈ N)
    {ι : Type*} (F : ι → E → ℂ) (hF : ∀ i, ContinuousOn (F i) N)
    (hH : ∀ z ∈ N, z ∈ H ↔ ∀ i, F i z = F i 0) : IsClosed (H : Set E) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hN 0 h0
  set ρ := r / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hcb : closedBall (0 : E) ρ ⊆ N :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hC : IsClosed (closedBall (0 : E) ρ ∩ (H : Set E)) := by
    have : closedBall (0 : E) ρ ∩ (H : Set E) =
        closedBall (0 : E) ρ ∩ ⋂ i, (closedBall (0 : E) ρ ∩ F i ⁻¹' {F i 0}) := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff,
        SetLike.mem_coe]
      constructor
      · rintro ⟨hz, hzH⟩
        exact ⟨hz, fun i => ⟨hz, (hH z (hcb hz)).mp hzH i⟩⟩
      · rintro ⟨hz, hi⟩
        exact ⟨hz, (hH z (hcb hz)).mpr fun i => (hi i).2⟩
    rw [this]
    exact isClosed_closedBall.inter (isClosed_iInter fun i =>
      ((hF i).mono hcb).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton)
  rw [← closure_subset_iff_isClosed]
  intro x hx
  obtain ⟨h, hh, hxh⟩ := Metric.mem_closure_iff.mp hx ρ hρpos
  have hy : x - h ∈ closure (H : Set E) := by
    have hcl : x - h ∈ H.topologicalClosure :=
      H.topologicalClosure.sub_mem hx (H.le_topologicalClosure hh)
    exact hcl
  have hyb : x - h ∈ ball (0 : E) ρ := by
    rw [mem_ball, dist_zero_right, ← dist_eq_norm]
    exact hxh
  have hyC : x - h ∈ closedBall (0 : E) ρ ∩ (H : Set E) := by
    have := isOpen_ball.inter_closure ⟨hyb, hy⟩
    have hsub : closure (ball (0 : E) ρ ∩ (H : Set E)) ⊆ closedBall (0 : E) ρ ∩ (H : Set E) :=
      closure_minimal (Set.inter_subset_inter_left _ ball_subset_closedBall) hC
    exact hsub this
  have : x = (x - h) + h := by abel
  rw [this]
  exact H.add_mem hyC.2 hh

end Closed

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex core `{v | ℂ v ⊆ H}` of an additive subgroup. -/
def ccore (H : AddSubgroup E) : Submodule ℂ E where
  carrier := {v | ∀ t : ℂ, t • v ∈ H}
  add_mem' := by
    intro a b ha hb t
    rw [smul_add]
    exact H.add_mem (ha t) (hb t)
  zero_mem' := by
    intro t
    rw [smul_zero]
    exact H.zero_mem
  smul_mem' := by
    intro c a ha t
    rw [smul_smul]
    exact ha _

theorem mem_ccore {H : AddSubgroup E} {v : E} : v ∈ ccore H ↔ ∀ t : ℂ, t • v ∈ H := Iff.rfl

theorem ccore_le_self {H : AddSubgroup E} {v : E} (hv : v ∈ ccore H) : v ∈ H := by
  simpa using hv 1

/-- **Identity theorem step: the real core of a subgroup cut out near `0` by holomorphic
functions is complex.** -/
theorem rcore_le_ccore (H : AddSubgroup E) (N : Set E) (hN : IsOpen N) (h0 : (0 : E) ∈ N)
    {ι : Type*} (F : ι → E → ℂ) (hF : ∀ i, DifferentiableOn ℂ (F i) N)
    (hH : ∀ z ∈ N, z ∈ H ↔ ∀ i, F i z = F i 0) {w : E} (hw : w ∈ rcore H) : w ∈ ccore H := by
  have hcont : Continuous fun t : ℂ => t • w := continuous_id.smul continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hN.preimage hcont) 0 (by simpa using h0)
  have hreal : ∀ r : ℝ, ((r : ℂ) • w) ∈ H := by
    intro r
    have := hw r
    rwa [← Complex.coe_smul] at this
  have hsmall : ∀ t ∈ ball (0 : ℂ) δ, t • w ∈ H := by
    intro t ht
    refine (hH _ (hball ht)).mpr fun i => ?_
    have hd : DifferentiableOn ℂ (fun t : ℂ => F i (t • w)) (ball (0 : ℂ) δ) :=
      (hF i).comp (differentiable_id.smul_const w).differentiableOn (fun s hs => hball hs)
    have han := hd.analyticOnNhd isOpen_ball
    have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => F i 0) (ball (0 : ℂ) δ) :=
      analyticOnNhd_const
    have hfreq : ∃ᶠ s in 𝓝[≠] (0 : ℂ), F i (s • w) = F i 0 := by
      have htend : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
        · have := (Complex.continuous_ofReal.tendsto 0).comp
            tendsto_one_div_add_atTop_nhds_zero_nat
          simpa [Function.comp_def] using this
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
          positivity
      refine htend.frequently (Eventually.frequently ?_)
      have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < δ :=
        tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hδ)
      filter_upwards [hev] with n hn
      have hb : ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) ∈ ball (0 : ℂ) δ := by
        rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        exact hn
      exact (hH _ (hball hb)).mp (hreal _) i
    exact han.eqOn_of_preconnected_of_frequently_eq hconst (convex_ball 0 δ).isPreconnected
      (mem_ball_self hδ) hfreq ht
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (‖t‖ / δ)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have htn : t / n ∈ ball (0 : ℂ) δ := by
    rw [mem_ball, dist_zero_right, norm_div, Complex.norm_natCast]
    rw [div_lt_iff₀ hδ] at hn
    rw [div_lt_iff₀ hnpos]
    linarith
  have : t • w = n • ((t / n) • w) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_div_cancel₀ _ hn0]
  rw [this]
  exact H.nsmul_mem (hsmall _ htn) n

/-- **The real core of a discrete subgroup is `0`.** -/
theorem eq_zero_of_mem_rcore_discrete (Λ : AddSubgroup E) [DiscreteTopology Λ] {v : E}
    (hv : v ∈ rcore Λ) : v = 0 := by
  let f : ℝ → Λ := fun t => ⟨t • v, hv t⟩
  have hf : Continuous f := (continuous_id.smul continuous_const).subtype_mk _
  have := PreconnectedSpace.constant inferInstance hf (x := 1) (y := 0)
  simpa [f] using congrArg Subtype.val this

end Complex

end ZInQ.ProductUnif

#print axioms ZInQ.ProductUnif.rcore_sup_eq_top
#print axioms ZInQ.ProductUnif.isClosed_of_local
#print axioms ZInQ.ProductUnif.rcore_le_ccore
#print axioms ZInQ.ProductUnif.eq_zero_of_mem_rcore_discrete
