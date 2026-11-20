import ZInQKernel.Contrib.OneProof.SphereCovectorVanishing
import ZInQKernel.Contrib.OneProof.ComplexLocalAntiderivative

/-! A holomorphic differential vanishes on the sphere. The local
representations are analytic coefficients times coordinate differentials. -/

noncomputable section

open Set
open scoped Topology Manifold ENNReal

variable {X E H : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H X] {I : ModelWithCorners ℂ E H}
  [I.Boundaryless] [IsManifold I 1 X]

/-- If each point of a complex manifold has a holomorphic local expression
for a covector field as an analytic coefficient times a coordinate
differential, the field vanishes when the manifold is a topological sphere. -/
theorem covector_eq_zero_of_holomorphic_local_coordinates_on_complex_sphere
    (e : X ≃ₜ OnePoint ℂ) (ω : ∀ x : X, TangentSpace I x →L[ℂ] ℂ)
    (hω : ∀ x : X, ∃ (U : Set X) (c : X → ℂ) (a : ℂ → ℂ), IsOpen U ∧ x ∈ U ∧
      MDifferentiableOn I 𝓘(ℂ, ℂ) c U ∧ AnalyticAt ℂ a (c x) ∧
      ∀ y ∈ U, ω y =
        (ContinuousLinearMap.toSpanSingleton ℂ (a (c y))).comp (mfderiv I 𝓘(ℂ, ℂ) c y)) :
    ∀ x, ω x = 0 := by
  apply covector_eq_zero_of_local_primitives_on_complex_sphere e ω
  intro x
  obtain ⟨U, c, a, hU, hx, hc, ha, hCoeff⟩ := hω x
  obtain ⟨g, r, hr, hg⟩ := ha.exists_complex_antiderivative
  let W := U ∩ c ⁻¹' Metric.eball (c x) r
  have hW : IsOpen W := hc.continuousOn.isOpen_inter_preimage hU Metric.isOpen_eball
  refine ⟨W, g ∘ c, hW, ⟨hx, Metric.mem_eball_self hr⟩, ?_, ?_⟩
  · intro y hy
    have hgy := (hg (c y) hy.2).2.differentiableAt.mdifferentiableAt
    have hcy := hc.mdifferentiableAt (hU.mem_nhds hy.1)
    exact (hgy.comp y hcy).mdifferentiableWithinAt
  · intro y hy
    have hgy := (hg (c y) hy.2).2.hasFDerivAt.hasMFDerivAt
    have hcy := (hc.mdifferentiableAt (hU.mem_nhds hy.1)).hasMFDerivAt
    exact (hgy.comp y hcy).mfderiv.trans (hCoeff y hy.1).symm

#print axioms covector_eq_zero_of_holomorphic_local_coordinates_on_complex_sphere
