import ZInQKernel.Contrib.OneProof.RC.X0Model.Expansion
import ZInQKernel.Contrib.OneProof.RC.CMField2.CosetLattice
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Topology.Algebra.Module.Cardinality

/-! # Parameters with transcendental j-value are dense

The j-function is holomorphic and nonconstant on the upper half-plane, so each of its fibres is
discrete and hence countable; the algebraic numbers are countable; a countable subset of the
plane has dense complement. -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric4

open Filter Topology UpperHalfPlane
open ZInQ.Manuscript.RC

/-- Each fibre of `j ∘ ofComplex` inside the upper half-plane is countable. -/
theorem countable_fibre_analyticJ (a : ℂ) :
    {z : ℂ | 0 < z.im ∧ X0Model.analyticJ (ofComplex z) = a}.Countable := by
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  let f : ℂ → ℂ := X0Model.analyticJ ∘ ofComplex
  have hf : AnalyticOnNhd ℂ f U := X0Model.analyticOn_j
  have hU : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected
  have hUo : IsOpen U := isOpen_upperHalfPlaneSet
  let Z := {z : ℂ | 0 < z.im ∧ X0Model.analyticJ (ofComplex z) = a}
  have hiso : ∀ z ∈ Z, ∀ᶠ w in 𝓝[≠] z, f w ≠ a := by
    rintro z ⟨hz, hza⟩
    rcases (hf z hz).eventually_eq_or_eventually_ne (analyticAt_const (v := a)) with h | h
    · exfalso
      have heq : Set.EqOn f (fun _ => a) U :=
        hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU hz h
      obtain ⟨τ, hτ⟩ := CMField2.exists_analyticJ_eq (a + 1)
      have := heq τ.im_pos
      simp only [f, Function.comp_apply, ofComplex_apply] at this
      rw [hτ] at this
      simp at this
    · exact h
  have hdisc : DiscreteTopology Z := by
    rw [discreteTopology_subtype_iff]
    intro z hz
    rw [Filter.inf_principal_eq_bot]
    exact (hiso z hz).mono fun w hw hwZ => hw hwZ.2
  have : Countable Z := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact Set.countable_coe_iff.mp this

/-- **(b3).** The parameters at which `j` takes a transcendental value are dense in the upper
half-plane. -/
theorem dense_transcendental_analyticJ :
    Dense {τ : ℍ | Transcendental ℚ (X0Model.analyticJ τ)} := by
  let B : Set ℂ := ⋃ a ∈ {a : ℂ | IsAlgebraic ℚ a},
    {z : ℂ | 0 < z.im ∧ X0Model.analyticJ (ofComplex z) = a}
  have hB : B.Countable :=
    (Algebraic.countable ℚ ℂ).biUnion fun a _ => countable_fibre_analyticJ a
  have hdense : Dense Bᶜ := hB.dense_compl ℝ
  rw [dense_iff_inter_open]
  intro V hV ⟨τ₀, hτ₀⟩
  have hVo : IsOpen ((↑) '' V : Set ℂ) := isOpenEmbedding_coe.isOpenMap V hV
  obtain ⟨z, ⟨τ, hτV, rfl⟩, hzB⟩ :=
    hdense.inter_open_nonempty _ hVo ⟨τ₀, τ₀, hτ₀, rfl⟩
  refine ⟨τ, hτV, fun halg => hzB ?_⟩
  refine Set.mem_biUnion (x := X0Model.analyticJ τ) halg ⟨τ.im_pos, ?_⟩
  rw [ofComplex_apply]

#print axioms countable_fibre_analyticJ
#print axioms dense_transcendental_analyticJ

end WeierstrassCurve.ModelLevels.ModelGeneric4
