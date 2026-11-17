
/-! ## The dictionary `IsAnalyticUnif ↔ IsAnalyticIso` -/

namespace HCMW

open WeierstrassCurve.Affine (Point)
open scoped PeriodPair
open ZInQ.Contrib.HCMDict (IsAnalyticUnif)

/-- Precomposing a local biholomorphism `ℂ → M` with `z ↦ γz` (`γ ≠ 0`). -/
theorem isLocalDiffeomorph_comp_mul {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {f : ℂ → M} (hf : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω f) {γ : ℂ} (hγ : γ ≠ 0) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (fun z => f (γ * z)) := by
  intro z
  obtain ⟨Φ, hzΦ, hfΦ⟩ := hf (γ * z)
  have hmul : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℂ => γ * z) :=
    contMDiff_iff_contDiff.mpr (contDiff_const.mul contDiff_id)
  have hdiv : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℂ => z / γ) :=
    contMDiff_iff_contDiff.mpr (contDiff_id.div_const γ)
  refine ⟨{ toFun := fun z => Φ (γ * z)
            invFun := fun Q => Φ.symm Q / γ
            source := (fun z => γ * z) ⁻¹' Φ.source
            target := Φ.target
            map_source' := fun w hw => Φ.map_source hw
            map_target' := fun Q hQ => by
              simp only [mem_preimage, mul_div_cancel₀ _ hγ]; exact Φ.map_target hQ
            left_inv' := fun w hw => by
              simp only [mem_preimage] at hw
              simp only [Φ.left_inv hw, mul_div_cancel_left₀ _ hγ]
            right_inv' := fun Q hQ => by
              simp only [mul_div_cancel₀ _ hγ, Φ.right_inv hQ]
            open_source := Φ.open_source.preimage (continuous_const.mul continuous_id)
            open_target := Φ.open_target
            contMDiffOn_toFun := Φ.contMDiffOn_toFun.comp hmul.contMDiffOn (fun w hw => hw)
            contMDiffOn_invFun := hdiv.comp_contMDiffOn Φ.contMDiffOn_invFun }, hzΦ, ?_⟩
  intro w hw
  exact hfΦ hw

section Short

variable {W : WeierstrassCurve ℂ} [W.IsElliptic] [W.IsShortNF]

theorem exists_ne_zero_point : ∃ P : W.toAffine.Point, P ≠ 0 := by
  obtain ⟨L, rfl⟩ := exists_lattice_eq_short W
  refine ⟨L.toPoint L.discriminant_ne_zero (L.ω₁ / 2), fun h => ?_⟩
  exact L.ω₁_div_two_notMem_lattice ((toPoint_eq_zero_iff L _).1 h)

/-- Two uniformizations of `E(ℂ)` in the clause form differ by a scaling `z ↦ γz`. -/
theorem exists_eq_unif_mul {Λ : Set ℂ} {ξ : ℂ → W.toAffine.Point} (hξ : IsAnalyticUnif W Λ ξ) :
    ∃ γ : ℂ, γ ≠ 0 ∧ ∀ z, ξ z = unif W (γ * z) := by
  have hu := (unif_props W).analyticUnif
  revert hu hξ
  generalize unif W = u
  intro hξ hu
  obtain ⟨L, rfl⟩ := exists_lattice_eq_short W
  obtain ⟨α, hα⟩ := ZInQ.Contrib.HCMDict.exists_eq_toPoint_mul L ξ hξ
  obtain ⟨β, hβ⟩ := ZInQ.Contrib.HCMDict.exists_eq_toPoint_mul L u hu
  have hne : ∀ (f : ℂ → L.weierstrassCurve.toAffine.Point) (a : ℂ), Function.Surjective f →
      (∀ z, f z = L.toPoint L.discriminant_ne_zero (a * z)) → a ≠ 0 := by
    rintro f a hf hfa rfl
    obtain ⟨P, hP⟩ := exists_ne_zero_point (W := L.weierstrassCurve)
    obtain ⟨z, rfl⟩ := hf P
    exact hP (by rw [hfa, zero_mul, L.toPoint_zero])
  have hα0 := hne ξ α hξ.2.1 hα
  have hβ0 := hne u β hu.2.1 hβ
  refine ⟨α / β, div_ne_zero hα0 hβ0, fun z => ?_⟩
  rw [hα, hβ]; congr 1; field_simp

/-- **Clause form ⇒ analytic isomorphism.** -/
theorem isAnalyticIso_of_isAnalyticUnif {Λ : Set ℂ} {ξ : ℂ → W.toAffine.Point}
    (hξ : IsAnalyticUnif W Λ ξ) : IsAnalyticIso W Λ ξ := by
  obtain ⟨γ, hγ, hξγ⟩ := exists_eq_unif_mul hξ
  have hfun : ξ = fun z => unif W (γ * z) := funext hξγ
  refine ⟨fun z w => ?_, hξ.2.1, ?_⟩
  · let ξh : ℂ →+ W.toAffine.Point := AddMonoidHom.mk' ξ hξ.1
    change ξh z = ξh w ↔ _
    rw [← sub_eq_zero, ← map_sub]
    exact hξ.2.2.1 _
  · rw [hfun]; exact isLocalDiffeomorph_comp_mul (unif_isLocalDiffeomorph W) hγ

/-- A local biholomorphism `ξ : ℂ → E(ℂ)` lifts locally through the chosen uniformization:
near every `z₀` there is a holomorphic `G` with `ξ = unif ∘ G`. -/
theorem exists_local_lift_unif {ξ : ℂ → W.toAffine.Point}
    (hξ : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω ξ) (z₀ : ℂ) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ z ∈ U, unif W (G z) = ξ z := by
  obtain ⟨w₀, hw₀⟩ := (unif_props W).analyticUnif.2.1 (ξ z₀)
  obtain ⟨Φ, hw₀Φ, hΦ⟩ := unif_isLocalDiffeomorph W w₀
  have hξc : Continuous ξ := hξ.contMDiff.continuous
  have hξd : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ξ := hξ.contMDiff
  set U := ξ ⁻¹' Φ.target
  have hU : IsOpen U := Φ.open_target.preimage hξc
  have hz₀U : z₀ ∈ U := by
    show ξ z₀ ∈ Φ.target
    rw [← hw₀, hΦ hw₀Φ]; exact Φ.map_source hw₀Φ
  refine ⟨U, hU, hz₀U, fun z => Φ.symm (ξ z), fun z hz => ?_, fun z hz => ?_⟩
  · have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Φ.symm (ξ z) :=
      (Φ.contMDiffOn_invFun (ξ z) hz).contMDiffAt (Φ.open_target.mem_nhds hz)
    have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun z => Φ.symm (ξ z)) z := h1.comp z (hξd z)
    rw [contMDiffAt_iff_contDiffAt] at h2
    exact (h2.differentiableAt (by simp)).differentiableWithinAt
  · have hs : Φ.symm (ξ z) ∈ Φ.source := Φ.map_target hz
    rw [hΦ hs]; exact Φ.right_inv hz

/-- **Analytic isomorphism with the group law ⇒ clause form.** -/
theorem isAnalyticUnif_of_isAnalyticIso {Λ : Set ℂ} {ξ : ℂ → W.toAffine.Point}
    (hξ : IsAnalyticIso W Λ ξ) (hadd : ∀ z w, ξ (z + w) = ξ z + ξ w) : IsAnalyticUnif W Λ ξ := by
  have h0 : ξ 0 = 0 := by
    have := hadd 0 0; rw [add_zero] at this
    exact left_eq_add.mp this
  refine ⟨hadd, hξ.2.1, fun z => ?_, fun z₀ hz₀ => ?_⟩
  · rw [← h0, hξ.1, sub_zero]
  · obtain ⟨U, hU, hz₀U, G, hGd, hG⟩ := exists_local_lift_unif hξ.2.2 z₀
    have hGz₀ : unif W (G z₀) ≠ 0 := by rw [hG z₀ hz₀U]; exact hz₀
    obtain ⟨U', hU', hGU', X, Y, hX, hY, hXY⟩ := (unif_props W).analyticUnif.2.2.2 (G z₀) hGz₀
    have hGc : ContinuousOn G U := hGd.continuousOn
    refine ⟨U ∩ G ⁻¹' U', hGc.isOpen_inter_preimage hU hU', ⟨hz₀U, hGU'⟩, X ∘ G, Y ∘ G,
      ?_, ?_, fun z hz => ?_⟩
    · intro z hz
      have hGz := (hGd z hz.1).differentiableAt (hU.mem_nhds hz.1)
      exact ((hX (G z) hz.2).differentiableAt (hU'.mem_nhds hz.2) |>.comp z hGz).differentiableWithinAt
    · intro z hz
      have hGz := (hGd z hz.1).differentiableAt (hU.mem_nhds hz.1)
      exact ((hY (G z) hz.2).differentiableAt (hU'.mem_nhds hz.2) |>.comp z hGz).differentiableWithinAt
    · obtain ⟨h, e⟩ := hXY (G z) hz.2
      exact ⟨h, by rw [← hG z hz.1, e]; rfl⟩

/-- **The dictionary.** The clause form `IsAnalyticUnif` of the hypothesis file is equivalent to `ξ`
being an analytic isomorphism `ℂ/Λ → E(ℂ)` (`IsAnalyticIso`, for the complex structure of `E(ℂ)` given
by the coordinate charts `x`, `y`, `t = -x/y`) that is a group homomorphism. -/
theorem isAnalyticUnif_iff_isAnalyticIso {Λ : Set ℂ} {ξ : ℂ → W.toAffine.Point} :
    IsAnalyticUnif W Λ ξ ↔ IsAnalyticIso W Λ ξ ∧ ∀ z w, ξ (z + w) = ξ z + ξ w :=
  ⟨fun h => ⟨isAnalyticIso_of_isAnalyticUnif h, h.1⟩,
    fun h => isAnalyticUnif_of_isAnalyticIso h.1 h.2⟩

/-- **The Weierstrass map is biholomorphic**: `z ↦ (℘_L(z), ℘'_L(z)/2)`, lattice points `↦ O`, is an
analytic isomorphism `ℂ/L → E_L(ℂ)`. -/
theorem toPoint_isAnalyticIso (L : PeriodPair) [L.weierstrassCurve.IsElliptic]
    [L.weierstrassCurve.IsShortNF] :
    IsAnalyticIso L.weierstrassCurve L.lattice (L.toPoint L.discriminant_ne_zero) :=
  isAnalyticIso_of_isAnalyticUnif (ZInQ.Contrib.HCMDict.toPoint_isAnalyticUnif L)

end Short

end HCMW
