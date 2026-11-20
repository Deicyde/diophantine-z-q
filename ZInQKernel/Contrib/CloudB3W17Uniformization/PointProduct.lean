import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Analytic inversion of the scheme-point product comparison

Attribution: the three analytic helper proofs below are adapted from host
`unif-printed`, Stage 2b, `UniformizationPrinted.lean` lines 426–570 at
`dbf043a4eb8d977b1d4bf0b03010f915b70bcfb8`. The host module is not on main.
We expose only the reusable analytic point-product comparison helpers here,
with genuine Mathlib manifolds and maps as hypotheses; no printed leaf or
scheme-point dictionary structure is introduced. This is not a new IFT proof:
the argument applies the existing normed implicit/inverse function theorems.
It complements the separate donor's vector-source/manifold-target IFT and is
needed to compare an independently charted product-point manifold with the
product of its factor-point manifolds.
-/

open scoped Manifold ContDiff Topology
open Set Filter Function

namespace CloudB3W17Uniformization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

section Inverse
variable {E2 F : Type*} [NormedAddCommGroup E2] [NormedSpace ℂ E2]
  [FiniteDimensional ℂ E2] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A locally injective map with surjective strict derivative has zero derivative kernel. -/
theorem ker_eq_bot_of_injOn {Ψ : E2 → F} {D : E2 →L[ℂ] F} {z₀ : E2}
    (hΨ : HasStrictFDerivAt Ψ D z₀) (hD : D.range = ⊤) {W : Set E2}
    (hW : W ∈ 𝓝 z₀) (hinj : InjOn Ψ W) : D.ker = ⊥ := by
  have : CompleteSpace E2 := FiniteDimensional.complete ℂ E2
  by_contra hne
  have : Nontrivial D.ker := Submodule.nontrivial_iff_ne_bot.mpr hne
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
  have : (𝓝[≠] (0 : D.ker)).NeBot := inferInstance
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

omit [IsManifold IN ω N] in
/-- A right inverse of an injective analytic comparison with surjective derivative is analytic. -/
theorem contMDiffAt_rightInverse (pr : M2 → N) (x₀ : M2)
    (hpr : ContMDiffAt 𝓘(ℂ, E2) IN ω pr x₀) (hinj : Injective pr)
    (hsurj : Surjective (mfderiv 𝓘(ℂ, E2) IN pr x₀)) (σ : N → M2)
    (hσ : ∀ y, pr (σ y) = y) : ContMDiffAt IN 𝓘(ℂ, E2) ω σ (pr x₀) := by
  have : CompleteSpace E2 := FiniteDimensional.complete ℂ E2
  set e2 := extChartAt 𝓘(ℂ, E2) x₀ with he2
  set eN := extChartAt IN (pr x₀) with heN
  set Ψ : E2 → F := eN ∘ pr ∘ e2.symm with hΨdef
  set z₀ := e2 x₀ with hz₀
  have hcont : ContinuousAt pr x₀ := hpr.continuousAt
  have hΨc : ContDiffAt ℂ ω Ψ z₀ := by
    have h := (contMDiffAt_iff.mp hpr).2
    simp only [modelWithCornersSelf_coe, range_id] at h
    exact contDiffWithinAt_univ.mp h
  have hΨz₀ : Ψ z₀ = eN (pr x₀) := by
    simp only [hΨdef, comp_apply, hz₀, he2, extChartAt_to_inv]
  set D := fderiv ℂ Ψ z₀ with hD
  have hstrict : HasStrictFDerivAt Ψ D z₀ := hΨc.hasStrictFDerivAt (by simp)
  have hmf : ∀ v, mfderiv 𝓘(ℂ, E2) IN pr x₀ v = D v := by
    intro v
    rw [(hpr.mdifferentiableAt (by simp)).mfderiv]
    simp [modelWithCornersSelf_coe, range_id, fderivWithin_univ, writtenInExtChartAt, hD,
      hΨdef, he2, heN, hz₀, tangentSpaceCastModel]
    rfl
  have hrange : D.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro w
    obtain ⟨v, hv⟩ := hsurj w
    exact ⟨v, (hmf v).symm.trans hv⟩
  set W : Set E2 := e2.target ∩ e2.symm ⁻¹' (pr ⁻¹' eN.source) with hWdef
  have hW : W ∈ 𝓝 z₀ := by
    refine Filter.inter_mem (extChartAt_target_mem_nhds x₀) ?_
    apply continuousAt_extChartAt_symm x₀
    rw [extChartAt_to_inv]
    exact hcont (extChartAt_source_mem_nhds (pr x₀))
  have hinjW : InjOn Ψ W := by
    intro z hz z' hz' heq
    have h1 : pr (e2.symm z) = pr (e2.symm z') := eN.injOn hz.2 hz'.2 heq
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
  have t1 : Tendsto eN (𝓝 (pr x₀)) (𝓝 (Ψ z₀)) := by
    rw [hΨz₀]; exact continuousAt_extChartAt (pr x₀)
  have ev1 := t1.eventually hs'.eventually_right_inverse
  have ev2 := t1.eventually (hs'.localInverse_tendsto.eventually hW)
  have ev3 : ∀ᶠ y in 𝓝 (pr x₀), y ∈ eN.source := extChartAt_source_mem_nhds _
  have heq : σ =ᶠ[𝓝 (pr x₀)] fun y => e2.symm (G (eN y)) := by
    filter_upwards [ev1, ev2, ev3] with y h1 h2 h3
    have h4 : pr (e2.symm (G (eN y))) = y := eN.injOn h2.2 h3 h1
    exact hinj (by rw [hσ y, h4])
  have c1 : ContMDiffAt IN 𝓘(ℂ, F) ω eN (pr x₀) := contMDiffAt_extChartAt
  have c2 : ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, E2) ω G (eN (pr x₀)) := by
    rw [← hΨz₀]; exact contMDiffAt_iff_contDiffAt.mpr hG
  have hGz : G (eN (pr x₀)) = z₀ := by rw [← hΨz₀]; exact hGimg
  have c3 : ContMDiffAt 𝓘(ℂ, E2) 𝓘(ℂ, E2) ω e2.symm (G (eN (pr x₀))) := by
    rw [hGz]
    exact (contMDiffOn_extChartAt_symm x₀ z₀ (mem_extChartAt_target x₀)).contMDiffAt
      (extChartAt_target_mem_nhds x₀)
  exact (ContMDiffAt.comp (pr x₀) c3 (c2.comp (pr x₀) c1)).congr_of_eventuallyEq heq
end Inverse

section Sections
variable {E E2 : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E2] [NormedSpace ℂ E2]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {M2 : Type*} [TopologicalSpace M2] [ChartedSpace E2 M2]

/-- Chain rule along a section of the point-product comparison. -/
theorem mfderiv_section_aux {N' : Type*} [TopologicalSpace N']
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℂ F' H'} [ChartedSpace H' N']
    (pr : M2 → N') (x₀ : M2) (hpr : MDifferentiableAt 𝓘(ℂ, E2) I' pr x₀)
    (s : M → M2) (P₀ : M) (hs : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀)
    (hs0 : s P₀ = x₀) (f : M → N') (hf : pr ∘ s = f) (u : E) :
    mfderiv 𝓘(ℂ, E2) I' pr x₀ (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀ u) =
      mfderiv 𝓘(ℂ, E) I' f P₀ u := by
  subst hs0 hf
  rw [mfderiv_comp P₀ hpr hs]
  rfl

/-- The two slice sections force the comparison derivative to be onto. -/
theorem surjective_mfderiv_of_sections (pr : M2 → M × M) (x₀ : M2)
    (hpr : MDifferentiableAt 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) pr x₀)
    (s t : M → M2) (P₀ Q₀ : M)
    (hs : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀)
    (ht : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E2) t Q₀)
    (hs0 : s P₀ = x₀) (ht0 : t Q₀ = x₀)
    (hs' : ∀ P, pr (s P) = (P, Q₀)) (ht' : ∀ Q, pr (t Q) = (P₀, Q)) :
    Surjective (mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) pr x₀) := by
  have e1 : ∀ u : E, mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) pr x₀
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀ u) = ((u, 0) : E × E) := by
    intro u
    rw [mfderiv_section_aux pr x₀ hpr s P₀ hs hs0 _ (funext hs'), mfderiv_prod_left]
    rfl
  have e2 : ∀ v : E, mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) pr x₀
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) t Q₀ v) = ((0, v) : E × E) := by
    intro v
    rw [mfderiv_section_aux pr x₀ hpr t Q₀ ht ht0 _ (funext ht'), mfderiv_prod_right]
    rfl
  rintro ⟨u, v⟩
  let a : TangentSpace 𝓘(ℂ, E2) x₀ := mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀ u
  let b : TangentSpace 𝓘(ℂ, E2) x₀ := mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) t Q₀ v
  refine ⟨a + b, ?_⟩
  rw [map_add]
  rw [show mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) pr x₀ a = ((u, 0) : E × E) from e1 u,
    show mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) pr x₀ b = ((0, v) : E × E) from e2 v]
  exact Prod.ext (add_zero u) (zero_add v)
end Sections

end
end CloudB3W17Uniformization
