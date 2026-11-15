import Mathlib

/-! # unif-printed, stage 2b: holomorphy of an inverse map (manifold glue, Mathlib only)

If `ι : M₂ → N` is holomorphic, injective, with surjective differential at `x₀`, then any right inverse of
`ι` is holomorphic at `ι x₀`. (The surjective differential plus injectivity gives, by the implicit function
theorem, an injective differential; then the analytic inverse function theorem applies.) For
`N = M × M`, surjectivity follows from holomorphic sections `P ↦ (P, Q₀)`, `Q ↦ (P₀, Q)`. -/

open scoped Manifold ContDiff Topology
open Set Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace UnifPrinted

section InvFun

variable {E2 F : Type*} [NormedAddCommGroup E2] [NormedSpace ℂ E2] [FiniteDimensional ℂ E2]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- **Implicit function theorem, injectivity form.** A map with surjective strict derivative that is
injective near the point has injective derivative. -/
theorem ker_eq_bot_of_injOn {Ψ : E2 → F} {D : E2 →L[ℂ] F} {z₀ : E2} (hΨ : HasStrictFDerivAt Ψ D z₀)
    (hD : D.range = ⊤) {W : Set E2} (hW : W ∈ 𝓝 z₀) (hinj : InjOn Ψ W) : D.ker = ⊥ := by
  by_contra hne
  haveI : Nontrivial D.ker := Submodule.nontrivial_iff_ne_bot.mpr hne
  set h := hΨ.implicitToOpenPartialHomeomorph Ψ D hD
  have h0 : h z₀ = (Ψ z₀, 0) := hΨ.implicitToOpenPartialHomeomorph_self hD
  have hsrc : z₀ ∈ h.source := hΨ.mem_implicitToOpenPartialHomeomorph_source hD
  have htgt : (Ψ z₀, (0 : D.ker)) ∈ h.target := hΨ.mem_implicitToOpenPartialHomeomorph_target hD
  have hsymm0 : h.symm (Ψ z₀, 0) = z₀ := by rw [← h0]; exact h.left_inv hsrc
  have hc : Continuous (fun k : D.ker => (Ψ z₀, k)) := continuous_const.prodMk continuous_id
  have hK : {k : D.ker | (Ψ z₀, k) ∈ h.target ∧ h.symm (Ψ z₀, k) ∈ W} ∈ 𝓝 (0 : D.ker) := by
    have h1 : h.target ∈ 𝓝 (Ψ z₀, (0 : D.ker)) := h.open_target.mem_nhds htgt
    have h2 : h.symm ⁻¹' W ∈ 𝓝 (Ψ z₀, (0 : D.ker)) := by
      apply h.continuousAt_symm htgt
      rw [hsymm0]; exact hW
    exact (hc.tendsto 0) (Filter.inter_mem h1 h2)
  have hne' : (𝓝[≠] (0 : D.ker)).NeBot := inferInstance
  obtain ⟨k, ⟨hkt, hkW⟩, hk0⟩ :=
    Filter.nonempty_of_mem (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hK)
      (self_mem_nhdsWithin : ({0}ᶜ : Set D.ker) ∈ 𝓝[≠] (0 : D.ker)))
  have hz1 : h (h.symm (Ψ z₀, k)) = (Ψ z₀, k) := h.right_inv hkt
  have hΨ1 : Ψ (h.symm (Ψ z₀, k)) = Ψ z₀ := by
    have := congrArg Prod.fst hz1
    rwa [hΨ.implicitToOpenPartialHomeomorph_fst] at this
  have heq := hinj hkW (mem_of_mem_nhds hW) hΨ1
  rw [heq, h0] at hz1
  exact hk0 (congrArg Prod.snd hz1).symm

variable {H : Type*} [TopologicalSpace H] {IN : ModelWithCorners ℂ F H}
  {M2 : Type*} [TopologicalSpace M2] [ChartedSpace E2 M2] [IsManifold 𝓘(ℂ, E2) ω M2]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold IN ω N]

/-- **Holomorphy of a right inverse.** -/
theorem contMDiffAt_rightInverse (ι : M2 → N) (x₀ : M2) (hι : ContMDiffAt 𝓘(ℂ, E2) IN ω ι x₀)
    (hinj : Function.Injective ι) (hsurj : Function.Surjective (mfderiv 𝓘(ℂ, E2) IN ι x₀))
    (σ : N → M2) (hσ : ∀ y, ι (σ y) = y) : ContMDiffAt IN 𝓘(ℂ, E2) ω σ (ι x₀) := by
  set e2 := extChartAt 𝓘(ℂ, E2) x₀ with he2
  set eN := extChartAt IN (ι x₀) with heN
  set Ψ : E2 → F := eN ∘ ι ∘ e2.symm with hΨdef
  set z₀ := e2 x₀ with hz₀
  have hcont : ContinuousAt ι x₀ := hι.continuousAt
  have hΨc : ContDiffAt ℂ ω Ψ z₀ := by
    have h := (contMDiffAt_iff.mp hι).2
    simp only [modelWithCornersSelf_coe, range_id] at h
    exact contDiffWithinAt_univ.mp h
  have hΨz₀ : Ψ z₀ = eN (ι x₀) := by
    simp only [hΨdef, Function.comp_apply, hz₀, he2, extChartAt_to_inv]
  set D := fderiv ℂ Ψ z₀ with hD
  have hstrict : HasStrictFDerivAt Ψ D z₀ := hΨc.hasStrictFDerivAt (by simp)
  have hmf : ∀ v, mfderiv 𝓘(ℂ, E2) IN ι x₀ v = D v := by
    intro v
    rw [(hι.mdifferentiableAt (by simp)).mfderiv]
    simp [modelWithCornersSelf_coe, range_id, fderivWithin_univ, writtenInExtChartAt, hD, hΨdef,
      he2, heN, hz₀, tangentSpaceCastModel]
    rfl
  have hrange : D.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro w
    obtain ⟨v, hv⟩ := hsurj w
    exact ⟨v, (hmf v).symm.trans hv⟩
  set W : Set E2 := e2.target ∩ e2.symm ⁻¹' (ι ⁻¹' eN.source) with hWdef
  have hW : W ∈ 𝓝 z₀ := by
    refine Filter.inter_mem (extChartAt_target_mem_nhds x₀) ?_
    apply continuousAt_extChartAt_symm x₀
    rw [extChartAt_to_inv]
    exact hcont (extChartAt_source_mem_nhds (ι x₀))
  have hinjW : InjOn Ψ W := by
    intro z hz z' hz' heq
    have h1 : ι (e2.symm z) = ι (e2.symm z') := eN.injOn hz.2 hz'.2 heq
    exact e2.symm.injOn (by simpa using hz.1) (by simpa using hz'.1) (hinj h1)
  have hker : D.ker = ⊥ := ker_eq_bot_of_injOn hstrict hrange hW hinjW
  let L : E2 ≃L[ℂ] F := (LinearEquiv.ofBijective (D : E2 →ₗ[ℂ] F)
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hrange⟩).toContinuousLinearEquiv
  have hL : (L : E2 →L[ℂ] F) = D := by ext v; rfl
  have hfd : HasFDerivAt Ψ (L : E2 →L[ℂ] F) z₀ := by rw [hL]; exact hstrict.hasFDerivAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set G := hΨc.localInverse hfd hn with hGdef
  have hG : ContDiffAt ℂ ω G (Ψ z₀) := hΨc.to_localInverse hfd hn
  have hs' := hΨc.hasStrictFDerivAt' hfd hn
  have hGimg : G (Ψ z₀) = z₀ := hΨc.localInverse_apply_image hfd hn
  have t1 : Tendsto eN (𝓝 (ι x₀)) (𝓝 (Ψ z₀)) := by
    rw [hΨz₀]; exact continuousAt_extChartAt (ι x₀)
  have ev1 := t1.eventually hs'.eventually_right_inverse
  have ev2 := t1.eventually (hs'.localInverse_tendsto.eventually hW)
  have ev3 : ∀ᶠ y in 𝓝 (ι x₀), y ∈ eN.source := extChartAt_source_mem_nhds _
  have heq : σ =ᶠ[𝓝 (ι x₀)] fun y => e2.symm (G (eN y)) := by
    filter_upwards [ev1, ev2, ev3] with y h1 h2 h3
    have h4 : ι (e2.symm (G (eN y))) = y := eN.injOn h2.2 h3 h1
    exact hinj (by rw [hσ y, h4])
  have c1 : ContMDiffAt IN 𝓘(ℂ, F) ω eN (ι x₀) := contMDiffAt_extChartAt
  have c2 : ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, E2) ω G (eN (ι x₀)) := by
    rw [← hΨz₀]; exact contMDiffAt_iff_contDiffAt.mpr hG
  have hGz : G (eN (ι x₀)) = z₀ := by rw [← hΨz₀]; exact hGimg
  have c3 : ContMDiffAt 𝓘(ℂ, E2) 𝓘(ℂ, E2) ω e2.symm (G (eN (ι x₀))) := by
    rw [hGz]
    exact (contMDiffOn_extChartAt_symm x₀ z₀ (mem_extChartAt_target x₀)).contMDiffAt
      (extChartAt_target_mem_nhds x₀)
  exact (ContMDiffAt.comp (ι x₀) c3 (c2.comp (ι x₀) c1)).congr_of_eventuallyEq heq

end InvFun

section Sections

variable {E E2 : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E2]
  [NormedSpace ℂ E2]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {M2 : Type*} [TopologicalSpace M2] [ChartedSpace E2 M2]

theorem mfderiv_section_aux {N' : Type*} [TopologicalSpace N'] {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℂ F'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℂ F' H'}
    [ChartedSpace H' N'] (ι : M2 → N') (x₀ : M2)
    (hι : MDifferentiableAt 𝓘(ℂ, E2) I' ι x₀) (s : M → M2) (P₀ : M)
    (hs : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀) (hs0 : s P₀ = x₀) (f : M → N')
    (hf : ι ∘ s = f) (u : E) :
    mfderiv 𝓘(ℂ, E2) I' ι x₀ (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀ u) =
      mfderiv 𝓘(ℂ, E) I' f P₀ u := by
  subst hs0 hf
  rw [mfderiv_comp P₀ hι hs]
  rfl

/-- **Surjectivity of `dι` from sections.** -/
theorem surjective_mfderiv_of_sections (ι : M2 → M × M) (x₀ : M2)
    (hι : MDifferentiableAt 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) ι x₀) (s t : M → M2) (P₀ Q₀ : M)
    (hs : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀) (ht : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E2) t Q₀)
    (hs0 : s P₀ = x₀) (ht0 : t Q₀ = x₀) (hs' : ∀ P, ι (s P) = (P, Q₀))
    (ht' : ∀ Q, ι (t Q) = (P₀, Q)) :
    Function.Surjective (mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) ι x₀) := by
  have e1 : ∀ u : E, mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) ι x₀
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀ u) = ((u, 0) : E × E) := by
    intro u
    rw [mfderiv_section_aux ι x₀ hι s P₀ hs hs0 _ (funext hs'), mfderiv_prod_left]
    rfl
  have e2 : ∀ v : E, mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) ι x₀
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) t Q₀ v) = ((0, v) : E × E) := by
    intro v
    rw [mfderiv_section_aux ι x₀ hι t Q₀ ht ht0 _ (funext ht'), mfderiv_prod_right]
    rfl
  rintro ⟨u, v⟩
  let a : TangentSpace 𝓘(ℂ, E2) x₀ := mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀ u
  let b : TangentSpace 𝓘(ℂ, E2) x₀ := mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) t Q₀ v
  refine ⟨a + b, ?_⟩
  rw [map_add]
  rw [show mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) ι x₀ a = ((u, 0) : E × E) from e1 u,
    show mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) ι x₀ b = ((0, v) : E × E) from e2 v]
  exact Prod.ext (add_zero u) (zero_add v)

end Sections

end UnifPrinted
