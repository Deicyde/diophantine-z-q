
/-! ## An analytic isomorphism `ℂ/Λ → E(ℂ)` sending `0` to `O` is a group homomorphism -/

namespace HCMW

open WeierstrassCurve.Affine (Point)
open scoped PeriodPair
open ZInQ.Contrib.HCMDict (IsAnalyticUnif)

section Short

variable {W : WeierstrassCurve ℂ} [W.IsElliptic] [W.IsShortNF]

instance compactSpacePoint : CompactSpace W.toAffine.Point :=
  (pointHomeo W).symm.compactSpace

/-- Two local lifts through `unif` have the same derivative. -/
theorem deriv_eq_of_lifts {G₁ G₂ : ℂ → ℂ} {z₀ : ℂ} (h₁ : DifferentiableAt ℂ G₁ z₀)
    (h₂ : DifferentiableAt ℂ G₂ z₀) (h : ∀ᶠ z in 𝓝 z₀, unif W (G₁ z) = unif W (G₂ z)) :
    deriv G₁ z₀ = deriv G₂ z₀ := by
  obtain ⟨ε, hε, hsmall⟩ := (unif_props W).small
  have hc : ContinuousAt (fun z => G₁ z - G₂ z) z₀ := h₁.continuousAt.sub h₂.continuousAt
  have hev : ∀ᶠ z in 𝓝 z₀, ‖(G₁ z - G₂ z) - (G₁ z₀ - G₂ z₀)‖ < ε := by
    have := hc.tendsto
    rw [Metric.tendsto_nhds] at this
    filter_upwards [this ε hε] with z hz; rwa [dist_eq_norm] at hz
  have hEq : G₁ =ᶠ[𝓝 z₀] fun z => G₂ z + (G₁ z₀ - G₂ z₀) := by
    filter_upwards [h, hev] with z hz hz'
    have hl : G₁ z - G₂ z ∈ unifΛ W := ((unif_props W).fib _ _).1 hz
    have hl0 : G₁ z₀ - G₂ z₀ ∈ unifΛ W :=
      ((unif_props W).fib _ _).1 (h.self_of_nhds)
    have := hsmall _ (sub_mem hl hl0) hz'
    linear_combination this
  rw [hEq.deriv_eq, deriv_add_const]

/-- **A biholomorphism `ℂ/Λ → E(ℂ)` sending `0` to `O` is `z ↦ unif(αz)`.** -/
theorem eq_unif_mul_of_isAnalyticIso {Λ : Set ℂ} {ξ : ℂ → W.toAffine.Point}
    (hξ : IsAnalyticIso W Λ ξ) (h0 : ξ 0 = 0) : ∃ α : ℂ, ∀ z, ξ z = unif W (α * z) := by
  have hu := unif_props W
  have hξc : Continuous ξ := hξ.2.2.contMDiff.continuous
  -- a compact set meeting every fibre of `ξ`
  obtain ⟨K, hK, hKf⟩ : ∃ K : Set ℂ, IsCompact K ∧ ∀ z, ∃ k ∈ K, ξ z = ξ k := by
    have hcov : (univ : Set W.toAffine.Point) ⊆ ⋃ z : ℂ, ξ '' Metric.ball z 1 := by
      intro P _
      obtain ⟨z, rfl⟩ := hξ.2.1 P
      exact mem_iUnion.mpr ⟨z, z, Metric.mem_ball_self one_pos, rfl⟩
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _
      (fun z => hξ.2.2.isOpenMap _ Metric.isOpen_ball) hcov
    refine ⟨⋃ z ∈ t, Metric.closedBall z 1, t.isCompact_biUnion fun z _ => isCompact_closedBall z 1,
      fun z => ?_⟩
    obtain ⟨i, hi, k, hk, hkz⟩ := mem_iUnion₂.mp (ht (mem_univ (ξ z)))
    exact ⟨k, mem_iUnion₂.mpr ⟨i, hi, Metric.ball_subset_closedBall hk⟩, hkz.symm⟩
  -- local lifts
  have hlift : ∀ z₀, ∃ r > 0, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball z₀ r) ∧
      ∀ z ∈ Metric.ball z₀ r, unif W (G z) = ξ z := by
    intro z₀
    obtain ⟨U, hU, hz₀U, G, hGd, hG⟩ := exists_local_lift_unif hξ.2.2 z₀
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀U
    exact ⟨r, hr, G, hGd.mono hrU, fun z hz => hG z (hrU hz)⟩
  choose rad hrad lift hliftd hlift using hlift
  have hliftD : ∀ z₀, ∀ z ∈ Metric.ball z₀ (rad z₀), DifferentiableAt ℂ (lift z₀) z :=
    fun z₀ z hz => (hliftd z₀ z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  set φ : ℂ → ℂ := fun z => deriv (lift z) z
  -- `φ` agrees near `z₀` with the derivative of the lift at `z₀`
  have hφloc : ∀ z₀, ∀ z ∈ Metric.ball z₀ (rad z₀), φ z = deriv (lift z₀) z := by
    intro z₀ z hz
    refine deriv_eq_of_lifts (hliftD z z (Metric.mem_ball_self (hrad z))) (hliftD z₀ z hz) ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hrad z)),
      Metric.isOpen_ball.mem_nhds hz] with w hw1 hw2
    rw [hlift z w hw1, hlift z₀ w hw2]
  have hφd : Differentiable ℂ φ := by
    intro z₀
    have han : AnalyticOnNhd ℂ (lift z₀) (Metric.ball z₀ (rad z₀)) :=
      (hliftd z₀).analyticOnNhd Metric.isOpen_ball
    have h1 : DifferentiableAt ℂ (deriv (lift z₀)) z₀ :=
      (han.deriv z₀ (Metric.mem_ball_self (hrad z₀))).differentiableAt
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hrad z₀))] with z hz
    exact hφloc z₀ z hz
  -- `φ` is constant on the fibres of `ξ`
  have hφfib : ∀ z k, ξ z = ξ k → φ z = φ k := by
    intro z k hzk
    set l := z - k
    have hl : l ∈ Λ := (hξ.1 z k).1 hzk
    have hG : ∀ᶠ w in 𝓝 z, unif W (lift z w) = unif W (lift k (w - l)) := by
      have hk : Metric.ball k (rad k) ∈ 𝓝 (z - l) := by
        simpa [l] using Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hrad k))
      have hk' : ∀ᶠ w in 𝓝 z, w - l ∈ Metric.ball k (rad k) :=
        (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds hk
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hrad z)), hk'] with w hw1 hw2
      rw [hlift z w hw1, hlift k _ hw2]
      exact (hξ.1 _ _).2 (by simpa [l] using hl)
    have hkd : DifferentiableAt ℂ (lift k) (z - l) := by
      simpa [l] using hliftD k k (Metric.mem_ball_self (hrad k))
    have := deriv_eq_of_lifts (hliftD z z (Metric.mem_ball_self (hrad z)))
      (hkd.comp z (differentiableAt_id.sub_const l)) hG
    simp only [φ]
    rw [this, deriv_comp_sub_const]
    simp [l]
  -- Liouville
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hφd.continuous.continuousOn
  have hbdd : Bornology.IsBounded (range φ) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨B, ?_⟩
    rintro _ ⟨z, rfl⟩
    obtain ⟨k, hk, hzk⟩ := hKf z
    rw [hφfib z k hzk]; exact hB k hk
  set α := φ 0
  have hφα : ∀ z, φ z = α := fun z => hφd.apply_eq_apply_of_bounded hbdd z 0
  -- clopen argument
  set S := {z : ℂ | ξ z = unif W (α * z)}
  have hSc : IsClosed S := isClosed_eq hξc (hu.continuous.comp (continuous_const.mul continuous_id))
  have hSo : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro z hz
    refine ⟨rad z, hrad z, fun w hw => ?_⟩
    have hconst : ∀ w ∈ Metric.ball z (rad z), lift z w - α * w = lift z z - α * z := by
      intro w hw
      have hd : ∀ v ∈ Metric.ball z (rad z), HasDerivAt (fun v => lift z v - α * v) 0 v := by
        intro v hv
        have h1 : HasDerivAt (lift z) α v := by
          rw [← hφα v, hφloc z v hv]; exact (hliftD z v hv).hasDerivAt
        have h2 : HasDerivAt (fun v => α * v) α v := by
          simpa using (hasDerivAt_id v).const_mul α
        simpa using h1.sub h2
      exact IsOpen.is_const_of_deriv_eq_zero (f := fun v => lift z v - α * v) Metric.isOpen_ball
        (convex_ball z (rad z)).isPreconnected
        (fun v hv => (hd v hv).differentiableAt.differentiableWithinAt)
        (fun v hv => (hd v hv).deriv) hw (Metric.mem_ball_self (hrad z))
    have hc : lift z z - α * z ∈ unifΛ W := by
      refine (hu.fib _ _).1 ?_
      rw [hlift z z (Metric.mem_ball_self (hrad z))]; exact hz
    show ξ w = unif W (α * w)
    rw [← hlift z w hw]
    refine (hu.fib _ _).2 ?_
    rw [show lift z w - α * w = lift z z - α * z from hconst w hw]; exact hc
  have h0S : (0 : ℂ) ∈ S := by
    show ξ 0 = unif W (α * 0)
    rw [h0, mul_zero, eq_comm, hu.analyticUnif.2.2.1]; exact zero_mem _
  have hS : S = univ := (IsClopen.eq_univ ⟨hSc, hSo⟩ ⟨0, h0S⟩)
  exact ⟨α, fun z => (hS ▸ mem_univ z : z ∈ S)⟩

/-- **A biholomorphism `ℂ/Λ → E(ℂ)` with `0 ↦ O` is a group homomorphism.** -/
theorem add_of_isAnalyticIso {Λ : Set ℂ} {ξ : ℂ → W.toAffine.Point}
    (hξ : IsAnalyticIso W Λ ξ) (h0 : ξ 0 = 0) : ∀ z w, ξ (z + w) = ξ z + ξ w := by
  obtain ⟨α, hα⟩ := eq_unif_mul_of_isAnalyticIso hξ h0
  intro z w
  rw [hα, hα, hα, mul_add]
  exact (unif_props W).analyticUnif.1 _ _

/-- **The dictionary, Shimura's reading.** `IsAnalyticUnif` (clause form) is equivalent to `ξ` being an
analytic isomorphism `ℂ/Λ → E(ℂ)` with `ξ(0) = O`; the group law is then automatic. -/
theorem isAnalyticUnif_iff_isAnalyticIso_zero {Λ : Set ℂ} {ξ : ℂ → W.toAffine.Point} :
    IsAnalyticUnif W Λ ξ ↔ IsAnalyticIso W Λ ξ ∧ ξ 0 = 0 := by
  rw [isAnalyticUnif_iff_isAnalyticIso]
  constructor
  · rintro ⟨h, hadd⟩
    refine ⟨h, ?_⟩
    have := hadd 0 0; rw [add_zero] at this
    exact left_eq_add.mp this
  · rintro ⟨h, h0⟩
    exact ⟨h, add_of_isAnalyticIso h h0⟩

end Short

end HCMW
