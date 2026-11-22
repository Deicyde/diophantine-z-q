import ZInQKernel.Contrib.OneProof.SphereLocalPrimitive
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Calculus.MeanValue

/-! A complex covector field admitting local holomorphic primitives
vanishes on a compact complex manifold homeomorphic to the sphere. -/

noncomputable section

open Set Filter
open scoped Topology Manifold

variable {X E H : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H X] {I : ModelWithCorners ℂ E H}
  [I.Boundaryless] [IsManifold I 1 X]

/-- A holomorphic function with zero derivative on an open set is locally
constant on that set. -/
theorem mdifferentiableOn_eventually_eq_of_mfderiv_eq_zero {g : X → ℂ} {U : Set X}
    (hU : IsOpen U) (hg : MDifferentiableOn I 𝓘(ℂ, ℂ) g U)
    (hd : ∀ y ∈ U, mfderiv I 𝓘(ℂ, ℂ) g y = 0) {x : X} (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x, g y = g x := by
  let c := extChartAt I x
  let V := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V := (continuousOn_extChartAt_symm (I := I) x).isOpen_inter_preimage
    (isOpen_extChartAt_target x) hU
  have hcx : c x ∈ V :=
    ⟨c.map_source (mem_extChartAt_source x), by
      simpa only [mem_preimage, c.left_inv (mem_extChartAt_source x)] using hx⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hV (c x) hcx
  let f : E → ℂ := g ∘ c.symm
  have hdf (z : E) (hz : z ∈ Metric.ball (c x) r) : fderiv ℂ f z = 0 := by
    have hz' := hsub hz
    have hsym := (mdifferentiableOn_extChartAt_symm (I := I) (x := x)).mdifferentiableAt
      ((isOpen_extChartAt_target x).mem_nhds hz'.1)
    have hgalg := (hg (c.symm z) hz'.2).mdifferentiableAt (hU.mem_nhds hz'.2)
    have hcomp := hgalg.hasMFDerivAt.comp z hsym.hasMFDerivAt
    rw [hd _ hz'.2, ContinuousLinearMap.zero_comp] at hcomp
    have hh := hcomp.mfderiv
    simp only [mfderiv_eq_fderiv] at hh
    apply ContinuousLinearMap.ext
    intro v
    let a := NormedSpace.fromTangentSpace (𝕜 := ℂ) z
    let b := NormedSpace.fromTangentSpace (𝕜 := ℂ) (f z)
    have h := congrArg (fun L => b (L (a.symm v))) hh
    simpa [a, b, f] using h
  have hf (z : E) (hz : z ∈ Metric.ball (c x) r) : DifferentiableAt ℂ f z := by
    have hz' := hsub hz
    have hsym := (mdifferentiableOn_extChartAt_symm (I := I) (x := x)).mdifferentiableAt
      ((isOpen_extChartAt_target x).mem_nhds hz'.1)
    have hgalg := (hg (c.symm z) hz'.2).mdifferentiableAt (hU.mem_nhds hz'.2)
    exact (hgalg.comp z hsym).differentiableAt
  have hBall (z : E) (hz : z ∈ Metric.ball (c x) r) : f z = f (c x) :=
    Metric.isOpen_ball.is_const_of_fderiv_eq_zero
      (convex_ball (c x) r).isPreconnected (fun z hz => (hf z hz).differentiableWithinAt)
      (fun z hz => hdf z hz) hz (Metric.mem_ball_self hr)
  have heV : ∀ᶠ y in 𝓝 x, c y ∈ Metric.ball (c x) r :=
    (continuousAt_extChartAt x).eventually (Metric.ball_mem_nhds _ hr)
  have hsource : ∀ᶠ y in 𝓝 x, y ∈ c.source :=
    (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
  filter_upwards [heV, hsource] with y hy hy'
  have hh := hBall (c y) hy
  simpa only [f, Function.comp_apply, c.left_inv hy',
    c.left_inv (mem_extChartAt_source x)] using hh

/-- On a complex manifold homeomorphic to the Riemann sphere, a covector
field that has local holomorphic primitives is everywhere zero. -/
theorem covector_eq_zero_of_local_primitives_on_complex_sphere
    (e : X ≃ₜ OnePoint ℂ) (ω : ∀ x : X, TangentSpace I x →L[ℂ] ℂ)
    (hω : ∀ x : X, ∃ (U : Set X) (g : X → ℂ), IsOpen U ∧ x ∈ U ∧
      MDifferentiableOn I 𝓘(ℂ, ℂ) g U ∧ ∀ y ∈ U, mfderiv I 𝓘(ℂ, ℂ) g y = ω y) :
    ∀ x, ω x = 0 := by
  choose U g hU hx hg hd using hω
  have hDiff (i j x : X) (hi : x ∈ U i) (hj : x ∈ U j) :
      ∀ᶠ y in 𝓝 x, g i y - g j y = g i x - g j x := by
    have hopen := (hU i).inter (hU j)
    have hgi := (hg i).mono (inter_subset_left : U i ∩ U j ⊆ U i)
    have hgj := (hg j).mono (inter_subset_right : U i ∩ U j ⊆ U j)
    apply mdifferentiableOn_eventually_eq_of_mfderiv_eq_zero hopen (hgi.sub hgj) _ ⟨hi, hj⟩
    intro y hy
    have hNy := hopen.mem_nhds hy
    rw [mfderiv_sub (hgi.mdifferentiableAt hNy) (hgj.mdifferentiableAt hNy),
      hd i y hy.1, hd j y hy.2]
    exact sub_self (ω y)
  intro x
  have he := local_primitives_eventually_constant_on_complex_sphere e U hU
    (fun x => ⟨x, hx x⟩) g hg hDiff x x (hx x)
  have hzero : HasMFDerivAt I 𝓘(ℂ, ℂ) (g x) x 0 :=
    (hasMFDerivAt_const (I := I) (I' := 𝓘(ℂ, ℂ)) (g x x) x).congr_of_eventuallyEq he
  exact (hd x x (hx x)).symm.trans hzero.mfderiv

#print axioms covector_eq_zero_of_local_primitives_on_complex_sphere
